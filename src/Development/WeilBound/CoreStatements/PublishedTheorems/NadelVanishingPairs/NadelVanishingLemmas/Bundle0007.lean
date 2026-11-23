module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGamma
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinateQuotientRegular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0045
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLatticeCohomologyVanish
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.cech_lattice_cohomology_vanish : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules) [F.IsQuasicoherent] {ι : Type} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens), LatModel M F → (∀ i, IsAffineOpen (U i)) → (∀ i, genericPoint X ∈ U i) → ⨆ i, U i = ⊤ → ∀ b : ℕ, 0 < b → (DI.CechZero (fun s => latSec M (inter U s)) b ↔ Subsingleton (coh F b)) := by
  first | exact @_root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh | exact _root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh | (intros; apply _root_.GlobalTheory.cechZero_latSec_iff_subsingleton_coh <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem mem_latSec_iff {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens)
    (v : V) : v ∈ latSec M U ↔ ∀ y ∈ U, v ∈ M y := by
  simp only [latSec, AddSubgroup.mem_iInf]

theorem latSec_anti {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) {U U' : X.Opens}
    (h : U' ≤ U) : latSec M U ≤ latSec M U' := fun v hv =>
  (mem_latSec_iff M U' v).2 fun y hy => (mem_latSec_iff M U v).1 hv y (h hy)

theorem forms_le_of_subset_of_subset {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {B B' : Set K}
    {L L' : Set V} (q : ℕ) (hB : B ⊆ B') (hL : L ⊆ L') : forms B L q ≤ forms B' L' q :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, hB hb, v, fun k => hL (hv k), e⟩

theorem f_dlog_of_frob {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (hf : IsF p π F f) (g : Kˣ) (z : Kt)
    (hz : π z = g) (hF : F z = z ^ p) : f (dlog g) = dlog g := by
  have key := hf.2 z 0 (by rw [hF]; ring)
  rw [map_zero, map_zero, add_zero, hz] at key
  have hp := (Fact.out : p.Prime)
  have e1 : ((g : K)⁻¹) ^ p * (g : K) ^ (p - 1) = (g : K)⁻¹ := by
    have hg : (g : K) ≠ 0 := g.ne_zero
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm ((g : K)⁻¹ ^ n), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hg, one_pow, mul_one]
  simp only [dlog, dK, Units.val_inv_eq_inv_val]
  rw [hf.1, key, smul_smul, e1]

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem decomp_of_isLifted : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  intro p _ X _ _ Z ι _ U n x W G H hnp hgen hcoord hW hlift hEff hdT hCart a b hHyp
  obtain ⟨Kt, _, π, F, hπ, hF, hz, hlog⟩ := hlift
  choose f hf using fun i => exists_isF_of_flatLift p π (F i) hπ (hF i)
  choose h hh using fun i j => exists_isH_of_isFrob p π (F i) (F j) hπ (hF i) (hF j)
  have hd := GlobalTheory.T.exterior_derivative_is_differential X.functionField
  have hdat := isDatum_of_frobenius_lifts p π F (extD X.functionField) f h hπ hF hd hf hh
  choose γ hγ using fun i => exists_isGamma p (f i) (hf i).1

  have hWmono : ∀ s t : Finset ι, s.Nonempty → s ⊆ t → W t ≤ W s := by
    intro s t hs hst y hy
    exact (hW s hs y).2 fun i hi => (hW t (hs.mono hst) y).1 hy i (hst hi)
  have hgenW : ∀ s : Finset ι, s.Nonempty → genericPoint X ∈ W s := fun s hs =>
    (hW s hs _).2 fun i _ => hgen i
  have hNuniv : ∀ a' (s : Finset ι), s.Nonempty →
      logSec Z G a' (W s) ≤ forms (Set.univ : Set X.functionField) (Set.univ : Set Ω[X.functionField⁄ℤ]) a' := by
    intro a' s hs v hv
    have := (mem_latSec_iff _ _ v).1 hv _ (hgenW s hs)
    exact forms_le_of_subset_of_subset a' (Set.subset_univ _) (Set.subset_univ _) this
  refine GlobalTheory.T.splitting_local_integrality (K := X.functionField) (V := Ω[X.functionField⁄ℤ]) p (extD X.functionField) f h γ
    (P := X) (fun s => {y | ∀ i ∈ s, y ∈ U i}) (fun y => locRing y) (fun y => {c | G.RegularAt y c})
    (fun y => dlog '' {g | LogUnit Z y g}) (fun q s => logSec Z G q (W s)) (fun q s => logSec Z H q (W s))
    hd.toIsOddDer hdat hγ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b hHyp
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s v hv
    exact hdT q s v hv
  · intro a' s hs
    exact hNuniv a' s hs
  · intro a' s hs hpa
    obtain ⟨i, -⟩ := id hs
    rw [eq_bot_iff]
    refine (hNuniv a' s hs).trans (le_of_eq ?_)
    exact spanForms_eq_bot_of_lt_card X.functionField n (x i) _ _ a' (hcoord i) (by omega)
  · intro a' s hs y hy v hv
    exact (mem_latSec_iff _ _ v).1 hv y ((hW s hs y).2 hy)
  · intro q s v hs _ hv
    refine (mem_latSec_iff _ _ v).2 fun y hy => ?_
    exact forms_le_of_subset_of_subset q (GlobalTheory.T.regular_functions_pth_power_twist p G H y hEff) subset_rfl (hv y ((hW s hs y).1 hy))
  · rintro s y hy i hi _ ⟨g, hg, rfl⟩
    obtain ⟨hfi, -⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    obtain ⟨w, hwA, hw⟩ := hfi i hi
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e, hw g.ne_zero, map_add (f := _), ← e]
    exact AddSubgroup.add_mem _ ((GlobalTheory.T.log_forms_generated_dlog Z y).2 g hg) ((GlobalTheory.T.log_forms_generated_dlog Z y).1 w hwA)
  · rintro s y hy i hi j hj _ ⟨g, hg, rfl⟩
    obtain ⟨-, hhij⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e]
    exact hhij i hi j hj
  · intro s j hj
    refine hCart s j hj (γ j) ⟨(hγ j).1, fun l => ?_⟩
    obtain ⟨z, hzx, hzF⟩ := hz j l
    rw [(hγ j).2, f_dlog_of_frob p π (F j) (f j) (hf j) (x j l) z hzx hzF]

end GlobalTheory.DI
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesFlatLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem isFlatLift_stalkMap_of_isEtCoord : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y), IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → ∀ (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ y : X, π y ∈ U → IsFlatLift p (π.stalkMap y).hom := by
  intro p _ Y X g f π hP U n t hU ht y hy
  obtain ⟨hs, hk⟩ := GlobalTheory.T.mod_p_squared_stalk_surjective p Y X g f π hP y
  have hfl := GlobalTheory.T.etale_coordinates_stalk_flat g U t hU ht (π y) hy
  refine ⟨hs, hk, fun w => ?_⟩
  rw [GlobalTheory.T.flat_mod_p_squared_torsion p _ hfl w, hk w]

end GlobalTheory.DI
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLatticeModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.exists_lattice_model : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V), (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) → ∃ F : X.Modules, Nonempty (LatModel M F) := by
  first | exact @_root_.GlobalTheory.LogDR.exists_latModel | exact _root_.GlobalTheory.LogDR.exists_latModel | (intros; apply _root_.GlobalTheory.LogDR.exists_latModel <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelFiniteQuasicoherent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.lattice_model_finite_quasicoherent : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F → (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧ LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔ ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | exact _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | (intros; apply _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelUniqueInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.lattice_model_unique_injective : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  first | exact @_root_.GlobalTheory.LogDR.latModel_map_and_unique | exact _root_.GlobalTheory.LogDR.latModel_map_and_unique | (intros; apply _root_.GlobalTheory.LogDR.latModel_map_and_unique <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogSectionsDifferentialClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory.LogDR

theorem extD_mem_logSec_roundedTwist : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (q : ℕ) (W : X.Opens) (η : abelian₂ X.functionField), η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) q W → extD _ η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) (q + 1) W := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr q W η hη
  simp only [logSec, latSec, AddSubgroup.mem_iInf] at hη ⊢
  intro y hy
  have hcov : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := (Opens.mem_iSup).1 hcov
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨-, hloc⟩ := _root_.GlobalTheory.roundedTwist_isEqn p 𝒜 G r hr
  obtain ⟨ρ, -, hρ⟩ := hloc i
  have heq := hρ y hi t ht
  have hstalk := GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) (p • G + ∑ c, r c • E c) y
    (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j)
  have h1 := hη y hy
  rw [hstalk q (𝒜.chart i) hi heq] at h1
  rw [hstalk (q + 1) (𝒜.chart i) hi heq]
  exact GlobalTheory.T.chart_forms_differential_closed X.functionField p (locRing y) n (𝒜.x i) (𝒜.J i) t ρ
    ((𝒜.chart i).chart y hi) q η h1

end GlobalTheory.LogDR
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.UnitOfHeightOnePrimes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

namespace GlobalTheory.EtUnit

theorem unit_mul_monomial_of_forall_height_one (R K : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (hπ : ∀ j ∈ J, IsUnit (π j) ∨ Prime (π j))
    (x : K) (hx : x ≠ 0)
    (h : ∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) →
      ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ x * algebraMap R K d = algebraMap R K c) :
    ∃ (u : Rˣ) (m : Fin n → ℤ), x = algebraMap R K u * ∏ j ∈ J, (algebraMap R K (π j)) ^ m j := by
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0' : b0 ≠ 0 := nonZeroDivisors.ne_zero hb0
  have hb0K : algebraMap R K b0 ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0'
  have ha0 : a0 ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨α, a, ha, hna⟩ := _root_.GlobalTheory.strip_prime_factors_target R π J a0 ha0
  obtain ⟨β, b, hb, hnb⟩ := _root_.GlobalTheory.strip_prime_factors_target R π J b0 hb0'
  have hπ0 : ∀ j ∈ J, π j ≠ 0 := fun j hj =>
    (hπ j hj).elim (fun hu => hu.ne_zero) (fun hp => hp.ne_zero)
  have han : a ≠ 0 := by rintro rfl; rw [zero_mul] at ha; exact ha0 ha
  have hbn : b ≠ 0 := by rintro rfl; rw [zero_mul] at hb; exact hb0' hb
  have hprodQ : ∀ (Q : Ideal R), Q.IsPrime → (∀ j ∈ J, π j ∉ Q) →
      ∀ e : Fin n → ℕ, ∏ j ∈ J, π j ^ e j ∉ Q := by
    intro Q hQ hQJ e hmem
    obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.associated_of_height_one_agree R π J a b han hbn hπ
    (fun j hj hp => ⟨hna j hj hp, hnb j hj hp⟩) (fun Q hQ h1 hQJ => by
      obtain ⟨c, d, hc, hd, hcd⟩ := h Q hQ h1 hQJ
      refine ⟨c * ∏ j ∈ J, π j ^ β j, d * ∏ j ∈ J, π j ^ α j,
        hQ.mul_notMem hc (hprodQ Q hQ hQJ β), hQ.mul_notMem hd (hprodQ Q hQ hQJ α), ?_⟩
      have e1 : algebraMap R K a0 * algebraMap R K d = algebraMap R K b0 * algebraMap R K c := by
        rw [← hcd]; field_simp
      have e2 : a0 * d = b0 * c := IsFractionRing.injective R K (by rw [map_mul, map_mul, e1])
      rw [ha, hb] at e2
      linear_combination e2)
  refine ⟨u, fun j => (α j : ℤ) - β j, ?_⟩
  have hK : ∀ j ∈ J, algebraMap R K (π j) ≠ 0 := fun j hj => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ0 j hj
  have hprodK : ∏ j ∈ J, algebraMap R K (π j) ^ ((α j : ℤ) - β j) =
      (∏ j ∈ J, algebraMap R K (π j) ^ α j) / ∏ j ∈ J, algebraMap R K (π j) ^ β j := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [zpow_sub₀ (hK j hj), zpow_natCast, zpow_natCast]
  have hβK : ∏ j ∈ J, algebraMap R K (π j) ^ β j ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => pow_ne_zero _ (hK j hj)
  have hbK : algebraMap R K b ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hbn
  rw [hprodK, ha, hb, hu]
  simp only [map_mul, map_prod, map_pow]
  field_simp

theorem unit_mul_monomial_iff : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (J : Finset (Fin n)) (ht : ∀ j, algebraMap A L (t j) ≠ 0) (g : Lˣ), (∀ Q : Ideal A, Q.IsPrime → Q ≤ P → (∀ j ∈ J, t j ∉ Q) → ∃ a b : A, a ∉ Q ∧ b ∉ Q ∧ (g : L) * algebraMap A L b = algebraMap A L a) ↔ ∃ (u : Lˣ) (m : Fin n → ℤ), (∃ a b : A, a ∉ P ∧ b ∉ P ∧ (u : L) * algebraMap A L b = algebraMap A L a) ∧ g = u * ∏ j ∈ J, Units.mk0 _ (ht j) ^ m j := by
  intro p _ A _ _ _ n t het P _ L _ _ _ J ht g
  constructor
  · intro hL
    letI : Algebra (MvPolynomial (Fin n) (ZMod p)) A :=
      (MvPolynomial.aeval (R := ZMod p) t).toRingHom.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin n) (ZMod p)) A := het
    haveI : IsRegularRing A := GlobalTheory.isRegularRing_of_etale (MvPolynomial (Fin n) (ZMod p)) A
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      IsRegularRing.isRegularLocalRing_localization P
    obtain ⟨hRd, hRi⟩ :=
      GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (Localization.AtPrime P)
    haveI : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    have hunits : ∀ y : P.primeCompl, IsUnit (algebraMap A L y) := fun y => by
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      rintro h0
      exact y.2 (h0 ▸ P.zero_mem)
    letI : Algebra (Localization.AtPrime P) L := (IsLocalization.lift hunits).toAlgebra
    haveI : IsScalarTower A (Localization.AtPrime P) L :=
      IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq hunits a).symm)
    haveI : IsFractionRing (Localization.AtPrime P) L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ L
    have hprime : ∀ j ∈ J, IsUnit (algebraMap A (Localization.AtPrime P) (t j)) ∨
        Prime (algebraMap A (Localization.AtPrime P) (t j)) := by
      intro j hj
      by_cases hjP : t j ∈ P
      · right
        refine GlobalTheory.T.regular_quotient_prime_element A P (t j) (fun h0 => ht j (by rw [h0, map_zero])) hjP
          (GlobalTheory.T.etale_coordinate_quotient_regular p A t het j)
      · left
        exact IsLocalization.map_units (Localization.AtPrime P) (⟨t j, hjP⟩ : P.primeCompl)
    obtain ⟨u, m, hum⟩ := unit_mul_monomial_of_forall_height_one (Localization.AtPrime P) L
      (fun j => algebraMap A (Localization.AtPrime P) (t j)) J hprime (g : L) g.ne_zero (by
        intro Q hQ _ hQJ
        have hQ'P : Q.comap (algebraMap A (Localization.AtPrime P)) ≤ P := by
          intro x hx
          by_contra hxP
          exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
            (IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl)))
        obtain ⟨a, b, ha, hb, hab⟩ := hL (Q.comap (algebraMap A (Localization.AtPrime P)))
          (Ideal.comap_isPrime _ Q) hQ'P (fun j hj hjQ => hQJ j hj hjQ)
        refine ⟨algebraMap A _ a, algebraMap A _ b, ha, hb, ?_⟩
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact hab)
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective P.primeCompl (u : Localization.AtPrime P)
    change IsLocalization.mk' (Localization.AtPrime P) a s = _ at has
    have haP : a ∈ P.primeCompl := by
      rw [← IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime P) P a s, has]
      exact u.isUnit
    refine ⟨Units.map (algebraMap (Localization.AtPrime P) L : Localization.AtPrime P →* L) u, m,
      ⟨a, s, haP, s.2, ?_⟩, ?_⟩
    · rw [Units.coe_map, MonoidHom.coe_coe, ← has, IsScalarTower.algebraMap_apply A
        (Localization.AtPrime P) L s, IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L a,
        ← map_mul, IsLocalization.mk'_spec]
    · ext
      rw [hum, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.coe_prod]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← IsScalarTower.algebraMap_apply]
  · rintro ⟨u, m, ⟨a, b, ha, hb, hab⟩, rfl⟩ Q hQ hQP hQJ
    have hK : ∀ j, algebraMap A L (t j) ≠ 0 := ht
    have hprodQ : ∀ e : Fin n → ℕ, ∏ j ∈ J, t j ^ e j ∉ Q := by
      intro e hmem
      obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hQJ j hj (hQ.mem_of_pow_mem _ hjm)
    refine ⟨a * ∏ j ∈ J, t j ^ (m j).toNat, b * ∏ j ∈ J, t j ^ (-m j).toNat,
      hQ.mul_notMem (fun h => ha (hQP h)) (hprodQ _),
      hQ.mul_notMem (fun h => hb (hQP h)) (hprodQ _), ?_⟩
    have key : ∀ j, algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat =
        algebraMap A L (t j) ^ (m j).toNat := by
      intro j
      have e : m j = ((m j).toNat : ℤ) - ((-m j).toNat : ℤ) := (Int.toNat_sub_toNat_neg _).symm
      calc algebraMap A L (t j) ^ m j * algebraMap A L (t j) ^ (-m j).toNat
          = algebraMap A L (t j) ^ (((m j).toNat : ℤ) - ((-m j).toNat : ℤ)) *
            algebraMap A L (t j) ^ (-m j).toNat := by rw [← e]
        _ = _ := by
          rw [zpow_sub₀ (hK j), zpow_natCast, zpow_natCast,
            div_mul_cancel₀ _ (pow_ne_zero _ (hK j))]
    rw [Units.val_mul, Units.coe_prod, map_mul, map_mul, map_prod, map_prod, ← hab]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_pow]
    rw [show (u : L) * (∏ j ∈ J, algebraMap A L (t j) ^ m j) *
        (algebraMap A L b * ∏ j ∈ J, algebraMap A L (t j) ^ (-m j).toNat) =
        (u : L) * algebraMap A L b * ∏ j ∈ J, (algebraMap A L (t j) ^ m j *
          algebraMap A L (t j) ^ (-m j).toNat) by rw [Finset.prod_mul_distrib]; ring]
    simp only [key]

end GlobalTheory.EtUnit
end

