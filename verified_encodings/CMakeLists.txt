# Verified-encoding (CakeML / cake_pb_cp) machinery: a curated table of small,
# deterministic .scp models that drive the full workflow-2 chain (solver ->
# cake_pb_cp -> veripb --elaborate -> cake_pb_cp) plus the opbdiff oracle. This
# is team tooling, kept separate from examples/ (which is user-facing material).
# The chain is driven by the shared run_scp_chain.bash here; scp_cases/ holds one
# curated .scp (and one skippable ctest) per cake-encodable constraint/form.
add_subdirectory(scp_cases)
