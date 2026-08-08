#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_PROBE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_CAKE_PROBE_HH

#include <cstdio>
#include <cstdlib>
#include <string>

/**
 * \file
 * \brief Measurement-only probe: run the workflow-2 cake_pb_cp chain over a
 * proof a test has just written.
 *
 * This is instrumentation, not part of the test harness. It is called from
 * verify_proof_and_dispose() in constraints_test_utils.hh, and does nothing at
 * all unless GCS_TEST_CAKE is set in the environment; when it is, it drives
 * cake_pb_cp and veripb through a shell and logs a greppable line per proof,
 * so the chain-verify rate across the random data-driven instances can be
 * measured. It never throws and never fails a test.
 *
 * It lives in its own header because none of that has anything to do with
 * writing a constraint test, and constraints_test_utils.hh -- which every
 * constraint test includes, and which a test author reads to find out how the
 * harness works -- is the wrong place to meet popen(), std::system() with
 * interpolated paths, and a hand-rolled output parser.
 *
 * \sa verified_encodings/run_scp_chain.bash, which runs the same chain as a
 * real test over a curated set of .scp cases.
 */

namespace gcs::test_innards
{
    // Runs the full verified-encoding chain on a just-written .scp/.pbp, best
    // effort, and logs a greppable "CAKECHAIN <name> <OUTCOME>" line. Never
    // throws: this is for measuring the chain-verify rate across the random
    // data-driven instances, not for gating the suite. Enabled by GCS_TEST_CAKE;
    // cake_pb_cp path overridable via CAKE_PB_CP.
#ifdef _WIN32
    // The probe drives cake_pb_cp and veripb through popen() and a POSIX shell,
    // and cake_pb_cp does not run on Windows anyway, so it compiles out to a
    // no-op there.
    inline auto cake_probe_chain(const std::string &) -> void
    {
    }
#else
    // Every shell-out below is deliberately best effort: the probe recovers from
    // a command that failed by inspecting what it did or did not write, and must
    // never fail a test. std::system() is declared with glibc's warn_unused_result
    // attribute, which -- unlike [[nodiscard]] -- a cast to void does not silence,
    // so funnel the calls through one helper whose name records the decision
    // rather than repeating an ignored return value at every site.
    inline auto cake_run_ignoring_status(const std::string & cmd) -> void
    {
        [[maybe_unused]] auto status = std::system(cmd.c_str());
    }

    inline auto cake_capture(const std::string & cmd) -> std::string
    {
        std::string out;
        if (FILE * p = ::popen((cmd + " 2>/dev/null").c_str(), "r")) {
            char buf[8192];
            size_t n;
            while ((n = std::fread(buf, 1, sizeof buf, p)) > 0)
                out.append(buf, n);
            ::pclose(p);
        }
        return out;
    }

    inline auto cake_probe_chain(const std::string & pn) -> void
    {
        if (auto e = std::getenv("GCS_TEST_CAKE"); ! (e && *e))
            return;
        const char * cakeenv = std::getenv("CAKE_PB_CP");
        std::string cake = (cakeenv && *cakeenv) ? cakeenv : "cake_pb_cp";
        auto scp = pn + ".scp", pbp = pn + ".pbp";
        auto vopb = pn + ".cakeopb", core = pn + ".cakecore";

        auto has = [](const std::string & s, const char * m) { return s.find(m) != std::string::npos; };
        // A VERIFIED line, or "s NO CONCLUSION": the latter is cake's success
        // output for a proof whose conclusion is NONE (the init-only tests).
        auto verified = [&](const std::string & s) { return has(s, "s VERIFIED") || has(s, "s NO CONCLUSION"); };
        auto lastmeaningful = [](const std::string & s) {
            std::string best;
            size_t i = 0;
            while (i < s.size()) {
                auto e = s.find('\n', i);
                auto line = s.substr(i, e == std::string::npos ? std::string::npos : e - i);
                if (! line.empty() && line.find("Running VeriPB") == std::string::npos)
                    best = line;
                if (e == std::string::npos)
                    break;
                i = e + 1;
            }
            return best;
        };
        auto log = [&](const std::string & outcome, const std::string & extra = "") {
            std::string line = "CAKECHAIN " + pn + " " + outcome;
            if (! extra.empty())
                line += " :: " + extra;
            line += "\n";
            std::fputs(line.c_str(), stderr);
        };

        // 1. cake_pb_cp re-derives its own OPB from the .scp.
        cake_run_ignoring_status(cake + " " + scp + " > " + vopb + " 2>/dev/null");
        std::string opb = cake_capture("cat " + vopb);
        if (opb.find(">=") == std::string::npos && opb.find("<=") == std::string::npos) {
            log("SKIP_NO_OPB");
            std::remove(vopb.c_str());
            return;
        }
        // 2. veripb elaborates OUR proof against CAKE's OPB (the divergence gate).
        // (A domain-{0} variable's zero-bit bound rows print with an EMPTY
        // left-hand side, which needs a veripb with the labelled-empty-LHS
        // parser fix of 2026-07-10.)
        auto elab = cake_capture("veripb " + vopb + " " + pbp + " --elaborate " + core + " 2>&1");
        if (! verified(elab)) {
            log("FAIL_ELAB", lastmeaningful(elab));
            // Preserve the failing triple (scp/pbp + cake's OPB) for inspection.
            // Uniquely numbered so multiple failures sharing a proof_name don't
            // overwrite each other.
            if (auto k = std::getenv("GCS_TEST_CAKE_KEEP"); k && *k) {
                static int fail_seq = 0;
                std::string dir{k}, sfx = std::to_string(++fail_seq);
                for (auto ext : {".scp", ".pbp"})
                    cake_run_ignoring_status("mkdir -p " + dir + " && cp " + pn + ext + " " + dir + "/" + pn + "." + sfx + ext + " 2>/dev/null");
                cake_run_ignoring_status("cp " + vopb + " " + dir + "/" + pn + "." + sfx + ".cakeopb 2>/dev/null");
            }
            std::remove(vopb.c_str());
            std::remove(core.c_str());
            return;
        }
        // 3. cake_pb_cp re-checks the elaborated core.
        auto rc = cake_capture(cake + " " + scp + " " + core);
        log(verified(rc) ? "OK" : "FAIL_RECHECK", lastmeaningful(rc));
        std::remove(vopb.c_str());
        std::remove(core.c_str());
    }
#endif
}

#endif
