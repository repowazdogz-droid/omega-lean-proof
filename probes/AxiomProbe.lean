-- Reproducibility probe: run with `lake env lean probes/AxiomProbe.lean` from the lean-proof/ root.
import OmegaV14
import OmegaP3Semantic
import OmegaP1Governance
import FailureProtocol

#check @OmegaP3Semantic.tamper_implies_collision
#check @OmegaP3Semantic.tamper_detection
#check @OmegaP3Semantic.canonicalBytes_injective_wf

#print axioms OmegaV14.all_twentytwo_conjuncts_sufficient
#print axioms OmegaV14.governed_iff_all_conjuncts
#print axioms OmegaV14.authorisation_condition

#print axioms OmegaP3Semantic.chain_integrity_extends
#print axioms OmegaP3Semantic.chain_monotonicity
#print axioms OmegaP3Semantic.tamper_implies_collision
#print axioms OmegaP3Semantic.tamper_detection
#print axioms OmegaP3Semantic.chain_no_gaps
#print axioms OmegaP3Semantic.canonicalBytes_injective_wf
#print axioms OmegaP3Semantic.decode_encode
#print axioms OmegaP3Semantic.old_axiom_was_false
#print axioms OmegaP3Semantic.old_axiom_was_false_seqnum

#print axioms OmegaP1Governance.governance_requires_contract
#print axioms OmegaP1Governance.governance_requires_agent

#print axioms retries_exceed_limit_implies_escalation
