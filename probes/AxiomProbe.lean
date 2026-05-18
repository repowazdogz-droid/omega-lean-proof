-- Reproducibility probe: run with `lake env lean probes/AxiomProbe.lean` from the lean-proof/ root to verify the axiom dependencies cited in the AISI/MATS/NIST drafts.
import OmegaV14
import OmegaP3Semantic
import OmegaP1Governance
import FailureProtocol

-- Type signatures of declared axioms
#check @OmegaP3Semantic.canonicalBytes_injective
#print OmegaP3Semantic.canonicalBytes_injective
#check @OmegaP3Semantic.compute_hash_collision_resistant
#print OmegaP3Semantic.compute_hash_collision_resistant

-- Axiom dependencies of each load-bearing theorem named in the drafts
#print axioms OmegaV14.all_twentytwo_conjuncts_sufficient
#print axioms OmegaV14.governed_iff_all_conjuncts
#print axioms OmegaV14.authorisation_condition

#print axioms OmegaP3Semantic.chain_integrity_extends
#print axioms OmegaP3Semantic.chain_monotonicity
#print axioms OmegaP3Semantic.tamper_detection
#print axioms OmegaP3Semantic.chain_no_gaps

#print axioms OmegaP3Semantic.canonicalBytes_injective
#print axioms OmegaP3Semantic.compute_hash_collision_resistant

#print axioms OmegaP1Governance.governance_requires_contract
#print axioms OmegaP1Governance.governance_requires_agent

#print axioms retries_exceed_limit_implies_escalation
