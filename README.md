# RUBIN Formal (Lean4) — bootstrap

Этот каталог содержит in-repo formal proof-pack baseline для RUBIN.

## Что есть сейчас

- Lean4-пакет `RubinFormal`
- `proof_coverage.json` с machine-readable coverage registry по всем 17 pinned section keys
- formal registry entries со статусами `proved` / `stated` и явными `notes` / `limitations` там, где claim scope уже не тянет на полное секционное доказательство

## Граница claims (критично)

Этот proof-pack — executable replay/refinement coverage для conformance-фикстур (CV-*.json) и baseline-слой
для дальнейшей формализации. Он нужен для воспроизводимого “якоря”, но **не** является универсальной
формальной верификацией CANONICAL.
Текущий machine-readable статус: `proof_level=refinement`, `claim_level=refined`.

Разрешённые формулировки (OK):

- "Lean executable semantics replay all conformance fixtures (CV-*.json)"
- "Go(reference) → Lean refinement is checked for critical ops over conformance fixture set"
- "Pinned-section coverage is machine-readable, but some section entries are intentionally `stated` or explicitly scope-limited"

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
- Формальный coverage registry сейчас явно отражает все 17 pinned section keys.
- Не все 17 записей имеют одинаковую силу: часть entries остаётся `stated`, а часть `proved` entries
  дополнительно ограничена `notes` / `limitations` в `proof_coverage.json`.
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

1. Углубить `stated` entries и scope-limited `proved` entries до более сильных секционных теорем там, где это действительно нужно.
2. Поддерживать `proof_coverage.json` в синхроне со `spec/SECTION_HASHES.json` и narrative в `rubin-spec`.
3. Не поднимать formal-only extra theorems в публичные pinned-section claims без явного registry update.
