# RUBIN Formal (Lean4)

Этот репозиторий содержит machine-checked formal proof surface для RUBIN.

## Что есть сейчас

- Lean4-пакет `RubinFormal`
- `proof_coverage.json` с machine-readable coverage registry по 24 текущим section entries
- formal registry entries с явным `evidence_level`, `notes` и `limitations`, чтобы публичные claims не обгоняли реальную границу доказательств

## Граница claims (критично)

Этот proof-pack — executable replay/refinement surface для conformance-фикстур (CV-*.json) и live Lean theorems
по части секций. Он даёт reproducible machine-checked evidence, но **не** является универсальной
формальной верификацией всего CANONICAL.
Текущий machine-readable статус: `proof_level=refinement`, `claim_level=refined`.

Разрешённые формулировки (OK):

- "Lean executable semantics replay all conformance fixtures (CV-*.json)"
- "Go(reference) → Lean refinement is checked for critical ops over conformance fixture set"
- "Pinned-section coverage is machine-readable with explicit evidence levels: universal, behavioral, assumption-backed, and contract-level"

Запрещённые формулировки (NOT OK):

- "formal verification of RUBIN consensus / CANONICAL"
- "bit-exact wire/serialization proven"
- "universal mechanized equivalence between spec text and Go/Rust implementations"

Источник истины по границе claims — `rubin-formal/proof_coverage.json` (`proof_level`, `claims`).
Дополнительно используется `claim_level` (`toy|byte|refined`) с CI-валидацией консистентности относительно `proof_level`.

Важно по wire-моделям:

- `RubinFormal.ByteWireV2` — реальная CompactSize / byte-accurate proof surface для текущих wire claims.
- `RubinFormal.ByteWireLegacy` — toy bootstrap-модель только для single-byte `CompactSize` (`n < 253`) и `TxMini`.

## Risk model / CI gate

- Док: `rubin-formal/RISK_MODEL.md`
- Lean validation в standalone репо: `lake build`
- Registry/claims lint в integrated workspace выполняются sibling-tooling из `../rubin-protocol/tools/`

## Что это значит

- Это **не** полный freeze-ready пакет уровня "универсальная байтовая модель wire + state transition для всех секций".
- Консенсусные правила не меняются.
- Формальный coverage registry сейчас содержит 24 machine-checked section entries.
- По силе claims текущая раскладка такая: `18` universal, `3` assumption-backed, `2` behavioral, `1` contract-level.
- Единый статус `proved` в registry не означает одинаковую силу claim: честная граница задаётся `evidence_level` и `limitations` в `proof_coverage.json`.
- Extra formal-only theorems не считаются pinned-section claims, если они не внесены в machine-readable registry.

## Локальный запуск

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --version
lake build
```

В integrated workspace можно использовать wrapper:

```bash
cd ../rubin-protocol && scripts/dev-env.sh -- bash -lc 'cd ../rubin-formal && lake build'
```

## Дальше

1. Поддерживать `proof_coverage.json`, public narrative и closeout evidence в синхроне.
2. Не поднимать formal-only extra theorems в публичные pinned-section claims без явного registry update.
3. Отдельно добрать theorem-level traceability (`theorem_refs`) как самостоятельный hygiene/improvement трек, не смешивая его с truth-correction.
