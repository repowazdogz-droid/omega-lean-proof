"""
OMEGA necessity harness — REAL (non-circular), all 15 v1.3 primitives.

Contract per primitive Pi:
  Fi = failure as a condition over DOMAIN variables (never names Pi)
  Necessity(Pi) := g1 & g2 & a & b
     g1: Fi alone SAT            (failure is a real reachable state)
     g2: 'Pi' not in symbols(Fi) (structural non-circularity guard)
     a : Fi & ¬Pi  SAT           (failure reachable without primitive)
     b : Fi & Pi   UNSAT         (primitive rules failure out)
  Verdict tag:
     CLEAN     - propositional encoding captures the failure faithfully
     AWKWARD   - propositional proxy; real failure is quantitative/temporal
     RESISTANT - cannot ground non-circularly in propositional logic
"""
from sympy import symbols
from sympy.logic.boolalg import And, Or, Not, Implies
from sympy.logic.inference import satisfiable

def sat(e):  return satisfiable(e) is not False
def unsat(e): return satisfiable(e) is False
def names(e): return {s.name for s in e.free_symbols}

def entails_positive(expr, var): return unsat(And(expr, Not(var)))
def entails_negative(expr, var): return unsat(And(expr, var))
def hard_no_flipped_shared_literal(F, P):
    for var in sorted(F.free_symbols & P.free_symbols, key=lambda s: s.name):
        f_pos, f_neg = entails_positive(F, var), entails_negative(F, var)
        p_pos, p_neg = entails_positive(P, var), entails_negative(P, var)
        if (f_pos and p_neg) or (f_neg and p_pos):
            return False, var.name
    return True, "no shared flipped literal"

S = symbols  # alias

# ---- domain variables, grouped by primitive concern -----------------------
# P1 governance
act_authorised, contract_present, agent_identified = S('act_authorised contract_present agent_identified')
# P2 reasoning
decision_made, reasoning_recorded, reasoning_substantive = S('decision_made reasoning_recorded reasoning_substantive')
# P3 traceability
record_committed, content_altered, hash_matches, alteration_detected = S('record_committed content_altered hash_matches alteration_detected')
# P4 expectation
action_committed, prior_stated, prior_falsifiable = S('action_committed prior_stated prior_falsifiable')
# P4M materiality
assumption_made, assumption_material, material_assumption_flagged = S('assumption_made assumption_material material_assumption_flagged')
# P4T trajectory / environment invariant
multi_step_plan, env_shifted, plan_revalidated = S('multi_step_plan env_shifted plan_revalidated')
# P5 confirmation
intent_formed, irreversible_action, gate_passed = S('intent_formed irreversible_action gate_passed')
# P5E execution attestation
payload_executed, executed_matches_approved = S('payload_executed executed_matches_approved')
# P6 delegation
action_taken, principal_accountable = S('action_taken principal_accountable')
# P6A aggregate materiality
substeps_individually_ok, aggregate_material, aggregate_assessed = S('substeps_individually_ok aggregate_material aggregate_assessed')
# P6L liability threshold
high_consequence_delegated, liability_owner_assigned = S('high_consequence_delegated liability_owner_assigned')
# PCF continuity
evaluator_used, anchor_fixed_ex_ante, metric_drifted = S('evaluator_used anchor_fixed_ex_ante metric_drifted')
# P10 competence attestation
authority_exercised, competence_claim_bound = S('authority_exercised competence_claim_bound')
# P11 expectation update integrity
expectation_updated, update_logged, silent_update = S('expectation_updated update_logged silent_update')
# P12 semantic integrity
expectation_stated, schema_bound, vacuous_expectation = S('expectation_stated schema_bound vacuous_expectation')

# ---- failure modes (domain conditions; none name their own primitive) -----
F1  = And(act_authorised, Not(contract_present))                                   # rogue authority
F2  = And(decision_made, reasoning_recorded, Not(reasoning_substantive))           # hollow reasoning (FM_R)
F3  = And(record_committed, content_altered, Not(alteration_detected))             # mutable history
F4  = And(action_committed, Not(prior_falsifiable))                                # no falsifiable prior
F4M = And(assumption_made, assumption_material, Not(material_assumption_flagged))  # decoy/material assumption hidden
F4T = And(multi_step_plan, env_shifted, Not(plan_revalidated))                     # stale trajectory
F5  = And(irreversible_action, Not(gate_passed))                                   # gate bypassed
F5E = And(payload_executed, Not(executed_matches_approved))                        # payload substitution
F6  = And(action_taken, Not(principal_accountable))                                # ungoverned delegation
F6A = And(substeps_individually_ok, aggregate_material, Not(aggregate_assessed))   # composition fallacy
F6L = And(high_consequence_delegated, Not(liability_owner_assigned))               # liability dumping
FCF = And(evaluator_used, metric_drifted, Not(anchor_fixed_ex_ante))               # Goodhart/anchor drift
F10 = And(authority_exercised, Not(competence_claim_bound))                        # recorded incompetence
F11 = And(expectation_updated, silent_update, Not(update_logged))                  # silent expectation update
F12 = And(expectation_stated, Not(schema_bound))                                   # vacuous expectation

# ---- primitives (constraints over the same domain variables) --------------
P1  = Implies(act_authorised, contract_present)
P2  = Implies(And(decision_made, reasoning_recorded), reasoning_substantive)
P3  = And(Implies(content_altered, Not(hash_matches)), Implies(Not(hash_matches), alteration_detected))
P4  = Implies(action_committed, prior_falsifiable)
P4M = Implies(And(assumption_made, assumption_material), material_assumption_flagged)
P4T = Implies(And(multi_step_plan, env_shifted), plan_revalidated)
P5  = Implies(irreversible_action, gate_passed)
P5E = Implies(payload_executed, executed_matches_approved)
P6  = Implies(action_taken, principal_accountable)
P6A = Implies(And(substeps_individually_ok, aggregate_material), aggregate_assessed)
P6L = Implies(high_consequence_delegated, liability_owner_assigned)
PCF = Implies(And(evaluator_used, metric_drifted), anchor_fixed_ex_ante)  # proxy: drift requires fixed anchor to be caught
P10 = Implies(authority_exercised, competence_claim_bound)
P11 = Implies(And(expectation_updated, silent_update), update_logged)
P12 = Implies(expectation_stated, schema_bound)

cases = [
 ("P1",P1,F1,"CLEAN","rogue/illegitimate authority"),
 ("P2",P2,F2,"AWKWARD","hollow reasoning (substantive is a proxy bool)"),
 ("P3",P3,F3,"CLEAN","mutable history"),
 ("P4",P4,F4,"CLEAN","no falsifiable prior"),
 ("P4M",P4M,F4M,"AWKWARD","material assumption hidden (materiality is quantitative)"),
 ("P4T",P4T,F4T,"AWKWARD","stale trajectory (temporal in reality)"),
 ("P5",P5,F5,"CLEAN","confirmation gate bypassed"),
 ("P5E",P5E,F5E,"CLEAN","payload substitution after approval"),
 ("P6",P6,F6,"CLEAN","ungoverned delegation"),
 ("P6A",P6A,F6A,"AWKWARD","composition fallacy (aggregate is quantitative)"),
 ("P6L",P6L,F6L,"AWKWARD","liability dumping (threshold is quantitative)"),
 ("PCF",PCF,FCF,"RESISTANT","Goodhart drift (genuinely about metric dynamics, not boolean)"),
 ("P10",P10,F10,"CLEAN","authority without competence basis"),
 ("P11",P11,F11,"CLEAN","silent expectation update"),
 ("P12",P12,F12,"CLEAN","vacuous expectation / no schema"),
]

print(f"{'PRIM':<5}{'g1':<6}{'g2':<6}{'(a)':<6}{'(b)':<6}{'NEC':<6}{'TAG':<10}failure")
print("-"*100)
clean_pass=awk_pass=res=0
for n,P,F,tag,desc in cases:
    g1=sat(F); g2=n not in names(F); a=sat(And(F,Not(P))); b=not sat(And(F,P))
    nec=g1 and g2 and a and b
    if nec and tag=="CLEAN": clean_pass+=1
    elif nec and tag=="AWKWARD": awk_pass+=1
    if tag=="RESISTANT": res+=1
    print(f"{n:<5}{str(g1):<6}{str(g2):<6}{str(a):<6}{str(b):<6}{('PASS' if nec else 'FAIL'):<6}{tag:<10}{desc}")
print("-"*100)
print(f"CLEAN necessity proven: {clean_pass}   AWKWARD (proxy, passes): {awk_pass}   RESISTANT (not propositional): {res}")

print()
print(f"{'PRIM':<5}{'HARD':<6}detail")
print("-"*100)
hard_clean_fail=[]
for n,P,F,tag,desc in cases:
    ok,detail=hard_no_flipped_shared_literal(F,P)
    print(f"{n:<5}{('PASS' if ok else 'FAIL'):<6}{detail}")
    if tag=="CLEAN" and not ok: hard_clean_fail.append(n)
print("-"*100)
if hard_clean_fail:
    print(f"HARD GUARD FAIL on CLEAN primitives: {', '.join(hard_clean_fail)}")
else:
    print("HARD GUARD: all 9 CLEAN primitives PASS (no shared flipped literal)")
