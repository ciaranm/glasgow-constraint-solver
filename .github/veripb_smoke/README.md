# VeriPB smoke fixture

`smoke.opb` / `smoke.pbp` are a small but real proof pair (a reified-equals
instance, complete enumeration of 8 solutions) captured from `equals_test`.
Proof checking is deterministic and platform-independent, so these exact bytes
verify identically everywhere.

They exist so the Windows CI lane (`.github/workflows/windows.yml`) can answer
"does VeriPB actually verify a proof on Windows?" without first building the
whole solver and its bash/veripb test harness. Regenerate with:

```
./build/equals_test        # writes equals_test_dup_equals.{opb,pbp} in CWD
cp equals_test_dup_equals.opb .github/veripb_smoke/smoke.opb
cp equals_test_dup_equals.pbp .github/veripb_smoke/smoke.pbp
veripb .github/veripb_smoke/smoke.opb .github/veripb_smoke/smoke.pbp   # sanity check
```
