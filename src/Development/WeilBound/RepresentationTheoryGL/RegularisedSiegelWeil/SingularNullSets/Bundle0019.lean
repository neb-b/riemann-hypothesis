module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.AddMemIffOfZero
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

variable {F : Type} [Field F] [NumberField F]

theorem add_mem_iff_of_zero {X : Type} [AddCommGroup X] {P : Set X} (h0 : (0 : X) ∈ P) {a b : X} (hab : a = 0 ∨ b = 0) :
    a + b ∈ P ↔ a ∈ P ∧ b ∈ P := by
  rcases hab with h | h <;> subst h <;> simp [h0]

theorem box_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : sndA F (h + y) ∈ boxA S' U ↔ sndA F h ∈ boxA S' U ∧ sndA F y ∈ boxA S' U := by
  have hz : ∀ v, h.2 v = 0 ∨ y.2 v = 0 := fun v => by
    by_cases hv : v ∈ S
    · exact Or.inr (ker_snd hε hy hv)
    · exact Or.inl (fix_snd hε hh hv)
  have hadd : ∀ v, (sndA F (h + y)) v = h.2 v + y.2 v := fun v => rfl
  simp only [boxA, Set.mem_ofPred_eq, hadd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).1,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).1⟩,
      ⟨fun v hv => ((add_mem_iff_of_zero (hU v) (hz v)).1 (h1 v hv)).2,
      fun v hv => ((add_mem_iff_of_zero (zero_mem _) (hz v)).1 (h2 v hv)).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨fun v hv => (add_mem_iff_of_zero (hU v) (hz v)).2 ⟨h1 v hv, h3 v hv⟩,
      fun v hv => (add_mem_iff_of_zero (zero_mem _) (hz v)).2 ⟨h2 v hv, h4 v hv⟩⟩

def tR (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : ℝ :=
  ρ (fstA F y) * (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem testT_eq (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v))
    (y : AF F) : testT ρ S U y = ((tR ρ S U y : ℝ) : ℂ) := by
  simp only [testT, tR, Set.indicator]
  split_ifs <;> simp

theorem tR_nonneg {ρ : Ainf F → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : 0 ≤ tR ρ S U y :=
  mul_nonneg (hρ _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

def bR (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℝ :=
  (boxA S U).indicator (fun _ => (1 : ℝ)) (sndA F y)

theorem tR_split {S S' : Finset (HeightOneSpectrum (𝓞 F))} (hSS : S ⊆ S') {ε : AF F} (hε : IsIdF S ε) (ρ : Ainf F → ℝ)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hU : ∀ v, (0 : Fv F v) ∈ U v) {h y : AF F} (hh : ε * h = h)
    (hy : ε * y = 0) : tR ρ S' U (h + y) = tR ρ S' U h * bR S' U y := by
  have hf : fstA F (h + y) = fstA F h := by
    rw [map_add (f := _), fst_eq y, ker_fst hε hy, add_zero]
  have hb := box_split hSS hε U hU hh hy
  unfold tR bR
  rw [hf]
  by_cases h1 : sndA F h ∈ boxA S' U <;> by_cases h2 : sndA F y ∈ boxA S' U
  · rw [Set.indicator_of_mem (hb.2 ⟨h1, h2⟩), Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h2 (hb.1 h').2), Set.indicator_of_notMem h2]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring
  · rw [Set.indicator_of_notMem (fun h' => h1 (hb.1 h').1), Set.indicator_of_notMem h1]; ring

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem small_eventually {ι A M : Type} [Finite ι] [TopologicalSpace A] [Zero A] [TopologicalSpace M]
    (R : (ι → A) → M) (hR : Continuous R) (U : Set M) (hU : IsOpen U) (h0 : R 0 ∈ U) (Sp : ℕ → Set A)
    (hSp : Tendsto Sp atTop (𝓝 0).smallSets) : ∀ᶠ k in atTop, ∀ w : ι → A, (∀ i, w i ∈ Sp k) → R w ∈ U := by
  have hW : R ⁻¹' U ∈ 𝓝 (0 : ι → A) := hR.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, tt, htt, hsub⟩ := hW
  have hN : (⋂ i, tt i) ∈ 𝓝 (0 : A) := Filter.iInter_mem.mpr htt
  filter_upwards [tendsto_smallSets_iff.mp hSp _ hN] with k hk w hw
  exact hsub (fun i _ => Set.mem_iInter.mp (hk (hw i)) i)

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem approxId_of (h1 : OneD) : ApproxId := by
  classical
  intro D t ψ hψ S e he lam hlam
  have hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_eq_succ (n := 1) hCM.2.2.1
  have : BorelSpace (AF D.host.F) := ⟨rfl⟩
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  obtain ⟨eA, heA⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_continuousAddEquiv D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  obtain ⟨-, hBd⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero D.host.F D.host.E D.sp.cm.sig hCM _ (Module.finBasis D.host.F D.host.E) t
  have hpair := _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord.pairHerm_eq_coordForm D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  generalize Module.finBasis D.host.F D.host.E = b at heA hBd hpair
  have hε0 : IsIdF S ((1, LIdemEx.indS S) : AF D.host.F) := ⟨rfl, fun v => rfl⟩
  obtain ⟨ε, hε, heS⟩ : ∃ ε : AF D.host.F, IsIdF S ε ∧ e = algebraMap (AF D.host.F) (AE D) ε :=
    ⟨_, hε0, e_eq D S e he⟩
  have hcA : cA D e = e := (LIdemEx.idem_props S e he).2
  obtain ⟨Θ, hΘ⟩ := exTheta' D t e ε heS hcA b eA heA
  have hcl : IsClosed ((fixE ε : AddSubgroup (AF D.host.F)) : Set (AF D.host.F)) :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have : LocallyCompactSpace (fixE ε) := hcl.locallyCompactSpace
  have : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨g1, G1, Sp, hg, hlim, hsupp, hSp⟩ := h1 D.host.F hCM.1 ψ hψ S ε hε (Measure.addHaar) inferInstance
  obtain ⟨c, -, hTr⟩ := transfer Θ lam (Measure.addHaar : Measure (fixE ε))
  set Bm := (coordForm D.sp.cm.sig b t).map (algebraMap D.host.F (AF D.host.F)) with hBm
  let sT : Mx D t t → _ := fun T => if hT : T ∈ hermA D t then
    Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hT⟩ else 0
  refine ⟨fun k x => ∏ i, g1 k (Θ x i), fun k T => if T ∈ hermA D t then (c : ℝ) * ∏ i, G1 k (sT T i) else 0,
    fun k => ⟨?_, ?_, fun T hT => ⟨?_, ?_⟩⟩, fun x => ?_, ?_⟩
  · exact (hTr (fun _ => g1 k)).2 (fun _ => (hg k).1)
  · intro x
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => (hg k).2.1 _)
  · beta_reduce
    rw [if_pos hT]
    exact mul_nonneg c.2 (Finset.prod_nonneg fun i _ => ((hg k).2.2 _).1)
  · beta_reduce
    have hpt : ∀ x : hermS D t e, pch ψ x.1.1 T = ∏ i, ψ ((Θ x i).1 * sT T i) := by
      intro x
      rw [pch_eq D t ψ x.1.1 T x.1.2 hT, hpair, dotProduct, char_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sT, dif_pos hT, hΘ, heA]
    calc ∫ x, (∏ i, g1 k (Θ x i)) * pch ψ x.1.1 T ∂lam
        = ∫ x, ∏ i, (fun i h => g1 k h * ψ (h.1 * sT T i)) i (Θ x i) ∂lam := by
          congr 1; funext x; rw [hpt, ← Finset.prod_mul_distrib]
      _ = (c : ℂ) * ∏ i, ∫ h, g1 k h * ψ (h.1 * sT T i) ∂(Measure.addHaar : Measure (fixE ε)) :=
          (hTr (fun i h => g1 k h * ψ (h.1 * sT T i))).1
      _ = _ := by
          rw [if_pos hT]
          push_cast
          congr 1
          exact Finset.prod_congr rfl fun i _ => ((hg k).2.2 _).2
  · have := tendsto_finsetProd Finset.univ (fun i _ => hlim (Θ x i))
    simpa using this
  · intro C hC hCT ε' hε'
    have hunit : IsUnit Bm.det := by
      have h := (RingHom.map_det (algebraMap D.host.F (AF D.host.F)) (coordForm D.sp.cm.sig b t)).symm
      rw [hBm]
      exact h ▸ (isUnit_iff_ne_zero.mpr hBd).map _
    let R : (Idx t (Module.finrank D.host.F D.host.E) → AF D.host.F) → Mx D t t := fun w => (eA.symm (Bm⁻¹ *ᵥ w)).1
    have hRc : Continuous R :=
      continuous_subtype_val.comp (eA.symm.continuous.comp (continuous_const.matrix_mulVec continuous_id))
    have hU : IsOpen {M : Mx D t t | -M ∉ C} := hC.isOpen_compl.preimage continuous_neg
    have h0 : R 0 ∈ {M : Mx D t t | -M ∉ C} := by
      have : R 0 = 0 := by simp [R, Matrix.mulVec_zero]
      simp only [Set.mem_ofPred_eq, this, neg_zero]
      exact fun h => (hCT 0 h).2.2 rfl
    filter_upwards [small_eventually R hRc _ hU h0 Sp hSp] with k hk T hTC
    obtain ⟨hTA, heT, -⟩ := hCT T hTC
    by_contra hlt
    have hpos := lt_trans hε' (not_le.mp hlt)
    beta_reduce at hpos
    rw [if_pos hTA] at hpos
    have hprod : ∀ i, G1 k (sT T i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne') i (Finset.mem_univ i)
    have hfixT : ∀ i, ε * sT T i = sT T i := by
      intro i
      simp only [sT, dif_pos hTA, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, coord_fix D t e ε heS b _ heT j]
    have hw : ∀ i, -(sT T i) ∈ Sp k := fun i => by
      have := hsupp k (sT T i) (hprod i)
      rwa [hfixT] at this
    have hmem := hk (fun i => -(sT T i)) hw
    have hR : R (fun i => -(sT T i)) = -T := by
      have h2 : (fun i => -(sT T i)) = -(Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hTA⟩) := by
        funext i; simp only [sT, dif_pos hTA, Pi.neg_apply]
      simp only [R, h2, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        map_neg, ← heA, eA.symm_apply_apply]
      rfl
    simp only [hR, neg_neg] at hmem
    exact hmem hTC

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId_B
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCutId

variable {D : D7} {n : ℕ}

theorem omega_fix {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D W.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)} (hω : IsWeilSch ψ χ θ W μ ω)
    {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    {g : G D n} (hg : proj D.sp.cm.sig (Jst D n) v g = 1) {y : hermA D n} (hy : IntAt v y) (X : Mx D W.rank n) :
    (ω g Ψ).1 X = pch ψ y.1 (ip W X X) * (ω g Ψ).1 X := by
  have e1 : ω (nb y * g) Ψ = ω g Ψ := by
    rw [nb_comm hnb hy.1 hy.2.1 hg, map_mul, Module.End.mul_apply, hΨ _ (nb_mem_KAt hnb hy)]
  have e2 := hω.unip (nb y) y.1 (hnb y) (ω g Ψ) X
  rw [map_mul, Module.End.mul_apply] at e1
  rw [e1] at e2
  exact e2

theorem ip_orbit (W : HSp D) (h : GA D W) (x : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (Formalism.L2.Theta.mt W h) (rat x)) (mm (Formalism.L2.Theta.mt W h) (rat x)) = rat (gramQ W x) := by
  rw [show gramQ W x = GlobalTheory.Unf.gramQ W x from rfl, GlobalTheory.Unf.FB.rat_gramQ]
  simp only [ip, mm]
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W) (Formalism.L2.Theta.mt W h),
    ← Matrix.mul_assoc (adj (Formalism.L2.Theta.mt W h)), GlobalTheory.MixModel.mt_unitary]

theorem rank_gram_le (W : HSp D) (x : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W x).rank ≤ x.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem law0 {B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ θ} {μ : Measure (Mx D B.rank n)}
    {ω : G D n →* Module.End ℂ (schwartzA θ B.rank n)} (hω : IsWeilSch ψ χ θ B μ ω)
    (Φ : schwartzA θ B.rank n) (s : ℂ) (hs : (B.rank : ℂ) / 2 = s + (n : ℂ) / 2) :
    IsLaw χ s (fun g => (ω g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  show (ω (q * g) Φ).1 0 = _ * _ * (ω g Φ).1 0
  have e' : ω (q * g) Φ = ω m (ω u (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D B.rank n) ⬝ a : Mx D B.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  rw [e', hω.levi m a hm, z1, hω.unip u b hu, z2, ← hs]
  simp [halfTr]

theorem resEta_add {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (k : ℕ) : ResEta D χ (r + 2 * k) :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one]⟩

theorem conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    conj (pch ψ x.1 (rat β.1)) = ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n))) := by
  have ht : Matrix.trace (mm x.1 (rat β.1)) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) x.1 : Mx D n n) :=
    Matrix.trace_mul_comm _ _
  change conj (ψ (halfTr (Matrix.trace (mm x.1 (rat β.1))))) = _
  rw [ht, AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]

theorem fc_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (lam : Measure (hermA D n)) (𝓖 : Set (hermA D n))
    (nb : hermA D n → G D n) (F : G D n → ℂ) (β : HermE D n) (g : G D n) :
    fc ψ lam 𝓖 nb F β g = ∫ x in 𝓖, F (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
  change (∫ b in 𝓖, F (nb b * g) * ψ (-halfTr ((β.1.map (incA D) * b.1).trace)) ∂lam) = _
  congr 1
  funext x
  rw [conj_pch hψ]

theorem cont_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) :
    Continuous fun x : hermA D n => conj (pch ψ x.1 (rat β.1)) :=
  Complex.continuous_conj.comp (hψ.1.comp (GlobalTheory.CompanionTheory.FourierN.continuous_halfTr.comp
    ((continuous_subtype_val.matrix_mul continuous_const).matrix_trace)))

theorem norm_conj_pch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (x : hermA D n) (β : HermE D n) :
    ‖conj (pch ψ x.1 (rat β.1))‖ ≤ 1 := by
  rw [Complex.norm_conj]
  exact (hψ.2.1 _).le

theorem intOn {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖) {f c : hermA D n → ℂ}
    (hf : Continuous f) (hp : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x) (hc : Continuous c) (hc1 : ∀ x, ‖c x‖ ≤ 1) :
    IntegrableOn (fun x => f x * c x) 𝓖 lam := by
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := n)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hb : ∀ x, ‖f x * c x‖ ≤ M := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hcov x
    rw [norm_mul, ← hp γ hγ x]
    calc ‖f (γ + x)‖ * ‖c x‖ ≤ ‖f (γ + x)‖ * 1 := mul_le_mul_of_nonneg_left (hc1 x) (norm_nonneg _)
      _ ≤ M := by rw [mul_one]; exact hM _ hx
  refine Measure.integrableOn_of_bounded (M := M) ?_ (hf.mul hc).aestronglyMeasurable ?_
  · rw [h.2.2]; exact ENNReal.one_ne_top
  · exact Eventually.of_forall hb

end PositivityTheory.Rg.Rsw.L.LCutId

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem eval_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → schwartzA θ W.rank n) (X : Mx D W.rank n) :
    (∑ i ∈ s, c i • f i).1 X = ∑ i ∈ s, c i * (f i).1 X := by
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem omega_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) (x : hermA D n)
    (Φ : schwartzA θ W.rank n) (X : Mx D W.rank n) : (ω (nb x) Φ).1 X = pch ψ x.1 (ip W X X) * Φ.1 X := by
  exact hω.unip (nb x) x.1 (hnb x) Φ X

theorem omega_cut (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) :
    (ω g Ψ').1 X = cutF ψ C (ip W X X) * (ω g Ψ).1 X := by
  subst hΨ'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  rw [eval_sum, show cutF ψ C (ip W X X) = ∑ x ∈ C.s, C.co x * pch ψ x.1 (ip W X X) from rfl,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hcomm : nb x * g = g * nb x :=
    PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts
      (PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_atPts hnb x (C.inf x hx) (C.off x hx)) hg
  rw [← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply,
    omega_nb hω hnb x, mul_assoc]

theorem pch_eq_one (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (Ψ : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (X : Mx D W.rank n) (hX : (ω g Ψ).1 X ≠ 0)
    (o : hermA D n) (ho : IntAt v o) : pch ψ o.1 (ip W X X) = 1 := by
  have hk := PositivityTheory.Rg.Rsw.L.LThBdd.nb_mem_KAt hnb o ho
  have hfix : ω (nb o) (ω g Ψ) = ω g Ψ := by
    rw [← Module.End.mul_apply, ← map_mul,
      PositivityTheory.Rg.Rsw.L.LThBdd.commute_of_atPts (Subgroup.mem_inf.mp hk).2 hg, map_mul,
      Module.End.mul_apply, hΨ _ hk]
  have h := omega_nb hω hnb o (ω g Ψ) X
  rw [hfix] at h
  exact mul_right_cancel₀ hX (h.symm.trans (one_mul _).symm)

theorem inner_rat' (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) = rat (gramQ W ξ) := by
  rw [show GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) =
      GlobalTheory.MixModel.adj (rat ξ) * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram W) * rat ξ) from rfl,
    ← GlobalTheory.MixModel.rat_conjTranspose, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul,
    ← GlobalTheory.MixModel.cT_sig]
  rfl

theorem ip_mt_rat (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) :
    ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ)) = rat (gramQ W ξ) := by
  calc ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))
      = GlobalTheory.MixModel.adj (mt W h⁻¹ * rat ξ) * (GlobalTheory.MixModel.gA W * (mt W h⁻¹ * rat ξ)) := rfl
    _ = GlobalTheory.MixModel.adj (rat ξ : Mx D W.rank n) *
          ((GlobalTheory.MixModel.adj (mt W h⁻¹) * (GlobalTheory.MixModel.gA W * mt W h⁻¹)) * rat ξ) := by
        rw [GlobalTheory.MixModel.adj_mul]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.StdUnn.inner W (rat ξ : Mx D W.rank n) (rat ξ) := by
        rw [GlobalTheory.MixModel.mt_unitary]
        rfl
    _ = rat (gramQ W ξ) := inner_rat' ξ

theorem rank_gramQ_le (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) : (gramQ W ξ).rank ≤ ξ.rank := by
  exact (Matrix.rank_mul_le_right _ _).trans (Matrix.rank_mul_le_right _ _)

theorem term_zero (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n} (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1)
    (h : GA D W) (ξ : Matrix (Fin W.rank) (Fin n) D.host.E) (hξ : ξ.rank ≠ W.rank) :
    (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) = 0 := by
  rw [omega_cut hω hnb C Ψ Ψ' hΨ' hg, ip_mt_rat]
  by_cases h0 : (ω g Ψ).1 (mm (mt W h⁻¹) (rat ξ)) = 0
  · rw [h0, mul_zero]
  · have hq : gramQ W ξ = ξᴴ * (Formalism.BasicNotions.HSpace.gram W * ξ) := by
      rw [← GlobalTheory.MixModel.cT_sig]
      rfl
    have hherm : ((gramQ W ξ).map ⇑(D.sp.cm.sig)).transpose = gramQ W ξ := by
      change Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (gramQ W ξ) = gramQ W ξ
      rw [GlobalTheory.MixModel.cT_sig, hq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose, Matrix.mul_assoc]
    have hlt : (gramQ W ξ).rank < W.rank :=
      (rank_gramQ_le ξ).trans_lt (lt_of_le_of_ne (Matrix.rank_le_height ξ) hξ)
    have hcut := hC (⟨gramQ W ξ, hherm⟩ : PositivityTheory.GramSchwartzFunctions.HermE D n) hlt (fun o ho => by
      have := pch_eq_one hω hnb Ψ hΨ hg _ h0 o ho
      rwa [ip_mt_rat] at this)
    rw [show cutF ψ C (rat (gramQ W ξ)) = 0 from hcut, zero_mul]

theorem theta_nb (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (x : hermA D n) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' (nb x * g) h =
      ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat y.1)) (mm (mt W h⁻¹) (rat y.1))) * (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  have hfun : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) =
        pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
          (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := by
    intro ξ
    rw [map_mul, Module.End.mul_apply]
    exact omega_nb hω hnb x _ _
  have hsub : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E =>
      pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
        (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆ {y | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hne
    apply hξ
    show _ * _ = 0
    rw [term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hne, mul_zero]
  calc theta ω Ψ' (nb x * g) h
      = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, ((ω (nb x * g)) Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := rfl
    _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
          pch ψ x.1 (ip W (mm (mt W h⁻¹) (rat ξ)) (mm (mt W h⁻¹) (rat ξ))) *
            (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ)) := tsum_congr hfun
    _ = _ := (tsum_subtype_eq_of_support_subset hsub).symm

theorem fix_open {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D} (C : Cut D n v) (Ψ Ψ' : schwartzA θ W.rank n)
    (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ) (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {k : G D n}
    (hk : k ∈ Ucut nb v C.s) (hkv : k ∈ atPts D.sp.cm.sig (Jst D n) {v}) : ω k Ψ' = Ψ' := by
  subst hΨ'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hc := PositivityTheory.Rg.Rsw.L.LThBdd.conj_mem_KAt hnb C hk hkv hx
  congr 1
  calc ω k (ω (nb x) Ψ) = ω (nb x * ((nb x)⁻¹ * k * nb x)) Ψ := by
        rw [show nb x * ((nb x)⁻¹ * k * nb x) = k * nb x by group, map_mul, Module.End.mul_apply]
    _ = ω (nb x) (ω ((nb x)⁻¹ * k * nb x) Ψ) := by rw [map_mul, Module.End.mul_apply]
    _ = ω (nb x) Ψ := by rw [hΨ _ hc]

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end

