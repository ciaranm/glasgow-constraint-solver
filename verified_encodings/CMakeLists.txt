# Verified-encoding (CakeML / cake_pb_cp) machinery: small, deterministic
# refutation models that drive the full workflow-2 chain (solver -> cake_pb_cp
# -> veripb --elaborate -> cake_pb_cp) plus the opbdiff oracle. This is team
# tooling, kept separate from examples/ (which is user-facing material). The
# chain is driven by the shared run_cake_pb_cp.bash here; each subdirectory adds
# one constraint's demo and its skippable test.
add_subdirectory(abs)
add_subdirectory(scp_cases)
