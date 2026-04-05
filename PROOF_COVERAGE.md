# Proof Coverage

Источник: `spec/SECTION_HASHES.json`  
Машинный реестр: `rubin-formal/proof_coverage.json`

Текущее состояние: machine-readable source-of-truth (`proof_coverage.json`) фиксирует
`proof_level=refinement`, `claim_level=refined`, полный registry по 25 current section entries и явные
`notes` / `limitations` для non-universal claims. Conformance-фикстуры
`conformance/fixtures/CV-*.json` покрыты Lean replay/refinement слоем.

## Термины (важно)

- `proof_level=refinement` означает: в репо есть исполняемый Lean replay-слой и trace-based
  Go(reference) → Lean refinement checks для критических ops на conformance-наборе.
- `claim_level` фиксирует допустимый публичный уровень заявлений:
  - `toy` (только model-baseline),
  - `byte` (byte-accurate слой),
  - `refined` (refinement to executable path).
- `status=proved/proved_with_axiom` относится к конкретной registry entry **в рамках указанного `proof_level`**.
- `status=proved_with_axiom` означает: proof закрывает секцию, но опирается на явно названные криптографические или модельные допущения, поэтому честный ceiling такой записи — `machine_checked_assumption_backed`, а не unconditional `universal`.
- `evidence_level` — главный public-facing taxonomy field. Именно он различает universal / behavioral / assumption-backed / contract-level ceiling.

Внешний аудит / freeze-ready коммуникации **НЕ ДОЛЖНЫ** трактовать текущий `proof_level=refinement`
как “formal verification of CANONICAL for all inputs/sections”.

Связка с hash-pinning:

- `proof_coverage.json` сейчас содержит 25 machine-checked registry entries.
- Все 25 текущих entries уже machine-checked; активных `stated` / `deferred` rows сейчас нет.
- Не все 25 entries равны по силе claims: честная граница определяется `evidence_level` и `limitations`.
- Extra formal-only theorems (например, `CORE_EXT` tightening) не считаются pinned-section coverage,
  если они не внесены отдельной registry entry.

## Текущая раскладка evidence levels

- `machine_checked_universal`: 19
- `machine_checked_assumption_backed`: 3
- `machine_checked_behavioral`: 2
- `machine_checked_contract`: 1

## Путь к freeze-ready

1. Держать матрицу покрытия в синхроне с public narrative и closeout evidence.
2. Углублять non-universal entries там, где это реально снижает consensus-risk или audit ambiguity.
3. Не смешивать truth-correction с отдельными hygiene lanes вроде theorem traceability.

## Risk scoring / gates

Профили готовности (Phase‑0/devnet/audit/freeze) и правила CI описаны в `rubin-formal/RISK_MODEL.md`.
В integrated workspace registry/claims lint запускаются из sibling-tooling в `../rubin-protocol/tools/`.

Локально:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
```

Integrated workspace:

```bash
cd ../rubin-protocol && scripts/dev-env.sh -- python3 tools/check_formal_coverage.py
cd ../rubin-protocol && scripts/dev-env.sh -- python3 tools/check_formal_risk_gate.py --profile phase0
cd ../rubin-protocol && scripts/dev-env.sh -- python3 tools/check_formal_refinement_bridge.py
cd ../rubin-protocol && scripts/dev-env.sh -- python3 tools/check_formal_claims_lint.py
```
