# Proof Coverage (bootstrap)

Источник: `spec/SECTION_HASHES.json`  
Машинный реестр: `rubin-formal/proof_coverage.json`

Текущее состояние: machine-readable source-of-truth (`proof_coverage.json`) фиксирует
`proof_level=refinement`, `claim_level=refined`, и явную формальную матрицу по 13 pinned section keys.
Conformance-фикстуры `conformance/fixtures/CV-*.json` покрыты Lean replay/refinement слоем.

## Термины (важно)

- `proof_level=refinement` означает: в репо есть исполняемый Lean replay-слой и trace-based
  Go(reference) → Lean refinement checks для критических ops на conformance-наборе.
- `claim_level` фиксирует допустимый публичный уровень заявлений:
  - `toy` (только model-baseline),
  - `byte` (byte-accurate слой),
  - `refined` (refinement to executable path).
- `status=proved/stated/deferred` относится к конкретной pinned-секции **в рамках указанного `proof_level`**.

Внешний аудит / freeze-ready коммуникации **НЕ ДОЛЖНЫ** трактовать текущий `proof_level=refinement`
как “formal verification of CANONICAL for all inputs/sections”.

Связка с hash-pinning:

- `spec/SECTION_HASHES.json` сейчас содержит 17 pinned section keys.
- `proof_coverage.json` явно покрывает 13 из них как formal registry entries.
- Остальные pinned keys считаются закрытыми только через conformance/CI evidence, если не добавлены
  отдельные formal entries.

## Путь к freeze-ready

1. Расширить formal registry до полного множества pinned section keys.
2. Углубить доказательства beyond-fixtures для consensus-critical safety-инвариантов.
3. Держать матрицу покрытия в синхроне с hash-pinning CANONICAL и narrative в spec docs.

## Risk scoring / gates

Профили готовности (Phase‑0/devnet/audit/freeze) и правила CI описаны в `rubin-formal/RISK_MODEL.md`.

Локально:

```bash
scripts/dev-env.sh -- python3 tools/formal_risk_score.py
scripts/dev-env.sh -- python3 tools/check_formal_risk_gate.py --profile phase0
scripts/dev-env.sh -- python3 tools/check_formal_refinement_bridge.py
scripts/dev-env.sh -- python3 tools/check_formal_claims_lint.py
```
