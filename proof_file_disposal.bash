# Shared proof-file disposal policy for the bash test wrappers.
#
# Source it, then call dispose_proof:
#
#   . "$(dirname "$0")/proof_file_disposal.bash"       # from the repo root
#   . "$(dirname "$0")/../proof_file_disposal.bash"    # from xcsp/, minizinc/, ...
#
# ctest invokes every wrapper by absolute path, so $0 names the script's own
# location whatever working directory the test runs in.
#
# The policy: delete a proof once it has verified, unless GCS_PRESERVE_PROOF_FILES
# asks for it to be kept. Proofs are large -- VeriPB .pbp files for enumeration
# tests routinely reach hundreds of megabytes -- and a full parallel ctest that
# kept them all could exhaust the disk mid-run and make an unrelated lane's proof
# write fail. A failing proof is always left behind to inspect, which needs no
# code here: every failure path in every wrapper exits before reaching disposal.
#
# The C++ harness applies the same policy to the proofs it writes itself; see
# dispose_of_proof_files in gcs/constraints/innards/constraints_test_utils.hh.
# It has a third state, GCS_PRESERVE_PROOF_FILES=all, which these wrappers
# deliberately treat the same as any other keep value: a wrapper runs its binary
# once, so there is no second instance for a counter to distinguish. That is
# explained in dev_docs/constraints.md.

# dispose_proof BASE [EXT...]
#
# Delete BASE.opb, BASE.pbp, BASE.scp and BASE.varmap, plus BASE.EXT for any
# extra extensions named. Only .opb and .pbp are always written; the rest appear
# for the runs that ask for them, and rm -f on an absent file is a no-op, so
# every extension can be handled unconditionally. Keep this list in step with
# proof_file_extensions on the C++ side.
dispose_proof() {
    local base=$1
    shift
    case "${GCS_PRESERVE_PROOF_FILES:-}" in
        '' | 0)
            local ext
            for ext in opb pbp scp varmap "$@" ; do
                rm -f "$base.$ext"
            done
            ;;
    esac
}
