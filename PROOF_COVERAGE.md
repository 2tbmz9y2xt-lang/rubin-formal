# Proof Coverage (bootstrap)

Источник: `spec/SECTION_HASHES.json`  
Машинный реестр: `rubin-formal/proof_coverage.json`

Текущее состояние: machine-readable source-of-truth (`proof_coverage.json`) фиксирует
`proof_level=refinement`, `claim_level=refined`, полный registry по 17 pinned section keys и явные
`notes` / `limitations` для thin или partial entries. Conformance-фикстуры
`conformance/fixtures/CV-*.json` покрыты Lean replay/refinement слоем.

## Термины (важно)

- `proof_level=refinement` означает: в репо есть исполняемый Lean replay-слой и trace-based
  Go(reference) → Lean refinement checks для критических ops на conformance-наборе.
- `claim_level` фиксирует допустимый публичный уровень заявлений:
  - `toy` (только model-baseline),
  - `byte` (byte-accurate слой),
  - `refined` (refinement to executable path).
- `status=proved/proved_with_axiom/stated/deferred` относится к конкретной pinned-секции **в рамках указанного `proof_level`**.
- `status=proved_with_axiom` означает: proof закрывает секцию, но опирается на явно названные криптографические или модельные допущения, поэтому честный ceiling такой записи — `machine_checked_assumption_backed`, а не unconditional `universal`.

Внешний аудит / freeze-ready коммуникации **НЕ ДОЛЖНЫ** трактовать текущий `proof_level=refinement`
как “formal verification of CANONICAL for all inputs/sections”.

Связка с hash-pinning:

- `spec/SECTION_HASHES.json` сейчас содержит 17 pinned section keys.
- `proof_coverage.json` теперь явно отслеживает все 17 ключей.
- Не все 17 entries равны по силе claims: часть оставлена как `stated`, а часть `proved`
  дополнительно ограничена `notes` / `limitations`.
- Extra formal-only theorems (например, `CORE_EXT` tightening) не считаются pinned-section coverage,
  если они не внесены отдельной registry entry.

## Путь к freeze-ready

1. Углубить `stated` entries и scope-limited `proved` entries до более сильных секционных теорем.
2. Углубить доказательства beyond-fixtures для consensus-critical safety-инвариантов.
3. Держать матрицу покрытия в синхроне с hash-pinning CANONICAL и narrative в spec docs.

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
