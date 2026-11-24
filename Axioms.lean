import UEF
import UEFReal
import UEFRoots
import UEFTime
import UEFBell
import UEFFields
import UEFGauss
import UEFEmergence
import UEFStandardModel
import UEFGolden
import UEFDark
import UEFGravity
import UEFHolography
import UEFTorus
import UEFTunneling
import UEFContainment
import UEFMoral
import UEFCycle
import UEFCollapse
import UEFBridges
import UEFRiemann
import UEFComplexity
import UEFFluids
import UEFGauge
import UEFElliptic
import UEFHodge
import UEFPoincare
import UEFErdos
import UEFPredictions

#print axioms UEF.the_one_equation
#print axioms UEF.Reals.transport
#print axioms UEF.Reals.proposition_8_6
#print axioms UEF.Reals.inv_phi
#print axioms UEF.Reals.kk_mode
#print axioms UEF.Reals.fibre_integral
#print axioms UEF.Roots.roots
#print axioms UEF.Roots.A1_9_every_ray
#print axioms UEF.Roots.A1_9
#print axioms UEF.Roots.lemma2
#print axioms UEF.Roots.spread
#print axioms UEF.Roots.lemma4
#print axioms UEF.Roots.conservation
#print axioms UEF.Roots.no_computable_is_random
#print axioms UEF.Roots.seeded_repeats
#print axioms UEF.Time.theorem6
#print axioms UEF.Time.time_requires_events
#print axioms UEF.Bell.chsh
#print axioms UEF.Bell.quantum_S
#print axioms UEF.Bell.no_predetermined_strategy
#print axioms UEF.Fields.positive_definite
#print axioms UEF.Fields.no_split
#print axioms UEF.Gauss.E32
#print axioms UEF.Gauss.A4
#print axioms UEF.Gauss.phase_invariant
#print axioms UEF.Gauss.charge_conserved
#print axioms UEF.Emergence.record_grows
#print axioms UEF.Emergence.labels_preserve_order
#print axioms UEF.StandardModel.quadratic_negative
#print axioms UEF.StandardModel.vacuum_is_minimum
#print axioms UEF.StandardModel.higgs_mass
#print axioms UEF.StandardModel.lambda_value
#print axioms UEF.StandardModel.asymptotic_freedom
#print axioms UEF.StandardModel.mass_ratio
#print axioms UEF.StandardModel.tan_sq_value
#print axioms UEF.StandardModel.weyl_count
#print axioms UEF.Golden.binary_partition
#print axioms UEF.Golden.whole
#print axioms UEF.Golden.theorem19
#print axioms UEF.Golden.invPhi_self_similar
#print axioms UEF.Dark.partition
#print axioms UEF.Dark.dark_measure_pos
#print axioms UEF.Dark.eta_planck
#print axioms UEF.Dark.units_forced
#print axioms UEF.Gravity.horizon_entropy
#print axioms UEF.Gravity.horizon_correction_iff
#print axioms UEF.Gravity.tortoise
#print axioms UEF.Gravity.ingoing_form
#print axioms UEF.Gravity.ingoing_det
#print axioms UEF.Gravity.ingoing_smooth
#print axioms UEF.Gravity.infall_crosses
#print axioms UEF.Gravity.infall_time
#print axioms UEF.Gravity.planck_energy
#print axioms UEF.Gravity.friedmann_acceleration
#print axioms UEF.Gravity.geodesic_equation
#print axioms UEF.Gravity.grr
#print axioms UEF.Gravity.flat_fixes_K
#print axioms UEF.Gravity.friedmann_second
#print axioms UEF.Holography.EF_zero_iff
#print axioms UEF.Holography.bridge_mass
#print axioms UEF.Holography.H_eq
#print axioms UEF.Torus.attack_detected
#print axioms UEF.Tunneling.closed_length
#print axioms UEF.Tunneling.radial_green
#print axioms UEF.Tunneling.Ccorr_one_iff
#print axioms UEF.Tunneling.lock_exists
#print axioms UEF.Containment.feasible_later
#print axioms UEF.Containment.contracts_to_ker
#print axioms UEF.Containment.gtc_strict
#print axioms UEF.Moral.energy_zero_iff
#print axioms UEF.Moral.free_energy_falls
#print axioms UEF.Cycle.tortoise
#print axioms UEF.Cycle.dust_conserved
#print axioms UEF.Cycle.winding_integer
#print axioms UEF.Collapse.minimizer_unique
#print axioms UEF.Collapse.identity_attractor
#print axioms UEF.Collapse.drift_log
#print axioms UEF.Collapse.laplace
#print axioms UEF.Collapse.coherence_one_iff
#print axioms UEF.Bridges.closure
#print axioms UEF.Bridges.constant_bridge
#print axioms UEF.Bridges.B5
#print axioms UEF.Riemann.transport_determinant
#print axioms UEF.Riemann.spectral_bridge
#print axioms UEF.Riemann.xi4_zero_iff
#print axioms UEF.Riemann.theorem_xi4_5
#print axioms UEF.Bridges.K7.certifiable_iff
#print axioms UEF.Bridges.invariant_tangent
#print axioms UEF.Bridges.cannot_stay
#print axioms UEF.Bridges.cannot_be_held
#print axioms UEF.Bridges.binary
#print axioms UEF.Bridges.one_opens_all
#print axioms UEF.Bridges.tests_spread
#print axioms UEF.Bridges.all_open_at_once
#print axioms UEF.Bridges.counterfactual_all
#print axioms UEF.Bridges.together
#print axioms UEF.Bridges.pinned_lock_iff
#print axioms UEF.Bridges.pinned_world
#print axioms UEF.Bridges.binary_existence
#print axioms UEF.Bridges.constantly_zero
#print axioms UEF.Complexity.Θ_injective
#print axioms UEF.Complexity.threshold
#print axioms UEF.Fluids.enstrophy
#print axioms UEF.Gauge.decoupling
#print axioms UEF.Gauge.transverse_mass
#print axioms UEF.Elliptic.sha_finite
#print axioms UEF.Hodge.steps_9_10
#print axioms UEF.Poincare.volume_bound
#print axioms UEF.Erdos.power_law
#print axioms UEF.Erdos.isometries_of_Z
#print axioms UEF.Erdos.erdos_AP
#print axioms UEF.Erdos.green_tao
#print axioms UEF.Predictions.F10_jarlskog
