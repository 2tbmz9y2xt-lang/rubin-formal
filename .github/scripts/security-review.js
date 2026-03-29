// DeepSeek hostile formal review — extracted from inline workflow script.
// Called by actions/github-script: await require('./.github/scripts/security-review.js')({github, context, core})

module.exports = async ({ github, context, core }) => {
  const fs = require('fs');
  const path = require('path');
  const { execSync } = require('child_process');
  const { jsonrepair } = require(
    path.join(process.env.JSONREPAIR_DIR, 'node_modules', 'jsonrepair')
  );

  const rawOutputPath = 'deepseek-raw-output.txt';
  const diff = fs.readFileSync('pr-diff.txt', 'utf8').slice(0, 128000);
  const prTitle = context.payload.pull_request?.title ?? '';
  const prBody = (context.payload.pull_request?.body ?? '').slice(0, 4000);

  const repoRoot = process.cwd();
  const repoRootReal = fs.realpathSync(repoRoot);
  const baseSha = process.env.BASE_SHA;
  const headSha = process.env.HEAD_SHA;

  // ── Detect changed files ────────────────────────────────
  const changedLeanFiles = execSync(
    `git diff --diff-filter=ACMR --name-only ${baseSha} ${headSha} -- '*.lean'`,
    { maxBuffer: 20 * 1024 * 1024 }
  )
    .toString()
    .split('\n')
    .map(s => s.trim())
    .filter(Boolean);

  const REGISTRY_FILES = [
    'proof_coverage.json',
    'refinement_bridge.json',
    'tools/check_formal_registry_truth.py',
  ];
  const changedRegistryFiles = execSync(
    `git diff --diff-filter=ACMR --name-only ${baseSha} ${headSha} -- ${REGISTRY_FILES.map(f => `'${f}'`).join(' ')}`,
    { maxBuffer: 1024 * 1024 }
  )
    .toString()
    .split('\n')
    .map(s => s.trim())
    .filter(Boolean);

  const JSON_REGISTRY_FILES = ['proof_coverage.json', 'refinement_bridge.json'];
  const changedJsonRegistryFiles = changedRegistryFiles.filter(f =>
    JSON_REGISTRY_FILES.includes(f)
  );
  const changedValidatorFiles = changedRegistryFiles.filter(
    f => !JSON_REGISTRY_FILES.includes(f)
  );
  const isRegistryOnly =
    changedJsonRegistryFiles.length > 0 &&
    changedLeanFiles.length === 0 &&
    changedValidatorFiles.length === 0;
  const isValidatorOnly =
    changedValidatorFiles.length > 0 &&
    changedLeanFiles.length === 0 &&
    changedJsonRegistryFiles.length === 0;

  // ── Safe file reader ────────────────────────────────────
  const readChangedFile = file => {
    const fullPath = path.resolve(repoRoot, file);
    const rel = path.relative(repoRoot, fullPath);
    if (rel.startsWith('..') || path.isAbsolute(rel)) {
      throw new Error(`Unsafe path outside repository: ${file}`);
    }
    const st = fs.lstatSync(fullPath);
    if (st.isSymbolicLink()) {
      throw new Error(`Refusing to read symlinked file: ${file}`);
    }
    if (!st.isFile()) {
      throw new Error(`Path is not a regular file: ${file}`);
    }
    const realPath = fs.realpathSync(fullPath);
    if (
      !(
        realPath === repoRootReal ||
        realPath.startsWith(`${repoRootReal}${path.sep}`)
      )
    ) {
      throw new Error(`Resolved file escapes repository root: ${file}`);
    }
    return fs.readFileSync(realPath, 'utf8');
  };

  // ── Build file payload for model context ────────────────
  const PER_FILE_CAP = 30000;
  const TOTAL_FILE_BUDGET = 100000;
  const SEPARATOR = '\n\n---\n\n';
  const entries = [];
  let usedBytes = 0;

  for (const file of changedLeanFiles) {
    let content;
    try {
      content = readChangedFile(file);
    } catch {
      continue;
    }
    const header = `FILE: ${file}\n`;
    const frameSize =
      header.length + (entries.length > 0 ? SEPARATOR.length : 0);
    if (usedBytes + frameSize + 200 > TOTAL_FILE_BUDGET) continue;
    const remainingBudget = TOTAL_FILE_BUDGET - usedBytes - frameSize;
    const contentBudget = Math.min(PER_FILE_CAP, remainingBudget);
    const entry = header + content.slice(0, contentBudget);
    entries.push(entry);
    usedBytes += entry.length + (entries.length > 1 ? SEPARATOR.length : 0);
  }

  for (const file of changedRegistryFiles) {
    let content;
    try {
      content = readChangedFile(file);
    } catch {
      continue;
    }
    const header = `REGISTRY FILE: ${file}\n`;
    const frameSize =
      header.length + (entries.length > 0 ? SEPARATOR.length : 0);
    if (usedBytes + frameSize + 200 > TOTAL_FILE_BUDGET) continue;
    const remainingBudget = TOTAL_FILE_BUDGET - usedBytes - frameSize;
    const contentBudget = Math.min(PER_FILE_CAP, remainingBudget);
    const entry = header + content.slice(0, contentBudget);
    entries.push(entry);
    usedBytes += entry.length + (entries.length > 1 ? SEPARATOR.length : 0);
  }

  const changedFilePayload = entries.join(SEPARATOR);

  // ── Previous findings dedup ─────────────────────────────
  const TRUSTED_AUTHORS = new Set(['github-actions[bot]']);
  let previousFindings = '';
  try {
    const allComments = [];
    for await (const response of github.paginate.iterator(
      github.rest.issues.listComments,
      {
        owner: context.repo.owner,
        repo: context.repo.repo,
        issue_number: context.issue.number,
        per_page: 100,
      }
    )) {
      allComments.push(...response.data);
    }
    const reviewComments = allComments
      .filter(
        c =>
          c.body &&
          TRUSTED_AUTHORS.has(c.user?.login ?? '') &&
          c.body.includes('Formal Review') &&
          c.body.includes('deepseek')
      )
      .slice(-3);
    if (reviewComments.length > 0) {
      const titles = [];
      for (const c of reviewComments) {
        const jsonMatch = c.body.match(/```json\n([\s\S]*?)```/);
        if (jsonMatch) {
          try {
            const parsed = JSON.parse(jsonMatch[1]);
            for (const f of parsed.findings || []) {
              const sev = String(f.severity || '')
                .replace(/[^A-Z]/g, '')
                .slice(0, 10);
              const title = String(f.title || '')
                .replace(/[\r\n]+/g, ' ')
                .replace(/[^\x20-\x7E]/g, '')
                .slice(0, 120);
              const file = String(f.file || '')
                .replace(/[^\x20-\x7E]/g, '')
                .slice(0, 200);
              if (sev && title) {
                titles.push(
                  `[${sev}] ${title}` + (file ? ` (in ${file})` : '')
                );
              }
            }
          } catch {}
        }
      }
      if (titles.length > 0) {
        previousFindings =
          '\n\nPREVIOUSLY REPORTED (do NOT re-report these — they are already tracked):\n' +
          [...new Set(titles)].join('\n');
      }
    }
  } catch (err) {
    core.warning(`Could not fetch previous reviews: ${err.message}`);
  }

  // ── Load system prompt from file ────────────────────────
  const systemPrompt = fs.readFileSync(
    path.join(repoRoot, '.github', 'prompts', 'deepseek-hostile-review.md'),
    'utf8'
  );

  // ── Build messages ──────────────────────────────────────
  const modelId = 'deepseek/DeepSeek-R1-0528';
  const reviewMessages = [
    { role: 'system', content: systemPrompt },
    {
      role: 'user',
      content: [
        `PR title:\n${prTitle}`,
        `PR body:\n${prBody}`,
        isRegistryOnly
          ? `PR type: REGISTRY-ONLY (no .lean changes — review JSON claim honesty)`
          : isValidatorOnly
            ? `PR type: VALIDATOR-ONLY (no .lean or JSON changes — review validator for weakening)`
            : '',
        changedLeanFiles.length > 0
          ? `Changed Lean files:\n${changedLeanFiles.join('\n')}`
          : '',
        changedRegistryFiles.length > 0
          ? `Changed registry files:\n${changedRegistryFiles.join('\n')}`
          : '',
        `Current changed file contents:\n\n${changedFilePayload}`,
        `PR diff:\n\n${diff}${previousFindings}`,
      ]
        .filter(Boolean)
        .join('\n\n'),
    },
  ];

  // ── Helpers ─────────────────────────────────────────────
  const stripOuterCodeFence = text => {
    let cleaned = typeof text === 'string' ? text : '';
    cleaned = cleaned.replace(/<think>[\s\S]*?<\/think>\s*/g, '');
    cleaned = cleaned
      .replace(/^\s*```(?:json)?\s*\n?/, '')
      .replace(/\n?\s*```\s*$/, '')
      .trim();
    return cleaned;
  };

  const parseReviewPayload = raw => {
    const normalized = stripOuterCodeFence(raw);
    if (!normalized) {
      return {
        parsed: null,
        candidate: normalized,
        normalized,
        error: new Error('empty model output'),
      };
    }
    try {
      return { parsed: JSON.parse(normalized), candidate: normalized, normalized };
    } catch (err) {
      try {
        const repaired = jsonrepair(normalized);
        core.warning(
          `Model returned malformed JSON: ${err.message}. jsonrepair succeeded.`
        );
        return {
          parsed: JSON.parse(repaired),
          candidate: normalized,
          normalized,
        };
      } catch (err2) {
        return {
          parsed: null,
          candidate: normalized,
          normalized,
          error: err2,
        };
      }
    }
  };

  // ── Call model ──────────────────────────────────────────
  const callModel = async useJsonMode => {
    const payload = {
      model: modelId,
      messages: reviewMessages,
      temperature: 0.6,
      top_p: 0.95,
    };
    if (useJsonMode) {
      payload.response_format = { type: 'json_object' };
    }
    const response = await fetch(
      'https://models.github.ai/inference/chat/completions',
      {
        method: 'POST',
        headers: {
          Accept: 'application/vnd.github+json',
          Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
          'X-GitHub-Api-Version': '2022-11-28',
          'Content-Type': 'application/json',
        },
        body: JSON.stringify(payload),
      }
    );
    if (!response.ok) {
      const body = await response.text();
      return { ok: false, status: response.status, body };
    }
    const data = await response.json();
    return {
      ok: true,
      content: data?.choices?.[0]?.message?.content ?? '',
    };
  };

  let result = null;
  try {
    core.info(`Trying model: ${modelId} with JSON mode`);
    let attempt = await callModel(true);
    if (!attempt.ok) {
      core.warning(
        `JSON mode request failed for ${modelId}: ${attempt.status}: ${(attempt.body || '').slice(0, 200)}`
      );
      core.info(`Retrying model: ${modelId} without JSON mode`);
      attempt = await callModel(false);
    }
    if (!attempt.ok) {
      throw new Error(
        `Security review model ${modelId} returned ${attempt.status}: ${(attempt.body || '').slice(0, 200)}`
      );
    } else {
      result = attempt.content;
    }
  } catch (err) {
    throw new Error(
      `Security review failed before validated findings were produced: ${err.message}`
    );
  }

  if (typeof result === 'string' && result.trim() !== '') {
    fs.writeFileSync(rawOutputPath, result, 'utf8');
  }

  // ── Parse and filter findings ───────────────────────────
  const parsedResult = parseReviewPayload(result);
  let parsed = parsedResult.parsed;
  if (!parsed) {
    const preview = (parsedResult.normalized || String(result || ''))
      .replace(/\s+/g, ' ')
      .slice(0, 180);
    throw new Error(
      `Security review produced invalid JSON from ${modelId}: ${parsedResult.error?.message || 'unknown parse error'}; preview=${preview}`
    );
  }

  const allChangedFiles = [...changedLeanFiles, ...changedRegistryFiles];
  const changedSet = new Set(allChangedFiles);
  const fileContents = new Map(
    allChangedFiles.map(file => {
      try {
        return [file, readChangedFile(file)];
      } catch {
        return [file, ''];
      }
    })
  );
  const lineCounts = new Map(
    allChangedFiles.map(file => [
      file,
      (fileContents.get(file) || '').split('\n').length,
    ])
  );

  const theoremRefsInText = text => {
    const out = new Set();
    const re = /`([A-Za-z0-9_.']+)`/g;
    let m;
    while ((m = re.exec(text || '')) !== null) {
      out.add(m[1]);
    }
    return [...out];
  };

  const normalizedFindings = Array.isArray(parsed.findings)
    ? parsed.findings
    : [];
  const filtered = [];
  const seen = new Set();
  for (const f of normalizedFindings) {
    if (!f || typeof f !== 'object') continue;
    if (!changedSet.has(f.file)) continue;
    if (!Number.isInteger(f.line) || f.line <= 0) continue;
    const maxLine = lineCounts.get(f.file) || 0;
    if (f.line > maxLine) continue;
    const content = fileContents.get(f.file) || '';
    const refs = theoremRefsInText(`${f.title || ''}\n${f.details || ''}`);
    // Skip phantom-ref filter for categories that report MISSING things
    const absenceCats = new Set([
      'OVERCLAIM',
      'PHANTOM',
      'BOUNDARY_GAP',
      'PHANTOM_DESYNC',
    ]);
    const cat = (f.category || '').toUpperCase();
    if (refs.length > 0 && !absenceCats.has(cat)) {
      const allMissing = refs.every(name => !content.includes(name));
      if (allMissing) continue;
    }
    const key = `${f.file}:${f.line}:${cat}`;
    if (seen.has(key)) continue;
    seen.add(key);
    filtered.push(f);
  }

  parsed.findings = filtered;
  if (parsed.degraded === true) {
    parsed.summary =
      'Security review degraded: model output was not valid JSON, so no validated findings were emitted. See raw artifact / workflow warning for details.';
  } else if (filtered.length === 0) {
    parsed.summary = 'No validated findings after stale/dup filtering.';
  } else if (
    typeof parsed.summary !== 'string' ||
    parsed.summary.trim() === ''
  ) {
    parsed.summary = `Filtered findings: ${filtered.length}.`;
  }

  core.setOutput('review', JSON.stringify(parsed, null, 2));
};
