module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
section
noncomputable section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem localAtT_of_overAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) (H : OverPlaceIntegralForm.OverAt L N v hv) :
    ∃ s, SplittingProjection.LocalAtT L N v hv s := by
  obtain ⟨P, Pb, s, hs, hfac, hker, ⟨iso⟩, hP, hPb, ⟨hle, -, hU⟩, b, φ, e, hfr, hbij, hφ, hrow, -⟩ := H
  have hs' : SplittingProjection.IsSplitting sp.cm.sig v s := ⟨hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  have hpart1 : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v (SplittingProjection.dualLb L)) :=
    SetLike.coe_injective ((coe_partOf_prP hs' _).trans (hP.trans (coe_partOf_prP hs' _).symm))
  have hpart2 : SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v N) =
      SplittingProjection.partOf (SplittingProjection.prPbar s) (SplittingProjection.locLat v L.Lb) :=
    SetLike.coe_injective ((coe_partOf_prPbar hs' _).trans (hPb.trans (coe_partOf_prPbar hs' _).symm))
  have hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b :=
    (isFrame_iff _ _).2 ((coe_partOf_prP hs' _).trans hfr)
  have huniq : ∀ g' : GL (Fin R.k) (v.adicCompletion F),
      ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (SplittingProjection.prP s) g.1 = g' :=
    existsUnique_upts sp.cm.sig sp.gram0 sp.baseGram_isHermitian (gram_matrix_det_unit sp) _ s hs'.2.1
  have hlev : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (SplittingProjection.prP s) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range := by
    intro g hg
    refine ⟨fun h => hbij.mapsTo h, fun h => ?_⟩
    obtain ⟨g', hg', hgg⟩ := hbij.surjOn h
    have h1 : bc (SplittingProjection.prP s) g' = bc (SplittingProjection.prP s) g :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g' * b =
        b⁻¹ * bc (SplittingProjection.prP s) g * b from hgg))
    have h2 : (⟨g', hg'.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g, hg⟩ :=
      (huniq (bc (SplittingProjection.prP s) g)).unique h1 rfl
    have h3 : g' = g := congrArg Subtype.val h2
    exact h3 ▸ hg'
  have hstab : ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔
        bc (SplittingProjection.prP s) g ∈ stabGL (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) :=
    fun g hg => (hlev g hg).trans (hb.mem_stabGL_iff _).symm
  obtain ⟨f, hf⟩ := hb.exists_fun φ
  let ε : L.fM v hv ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F) := e
  have hfe : ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f y = ε (L.fT v hv x) := by
    intro x y hxy
    obtain ⟨z, hz⟩ := hb.exists_coord y
    exact (hf y z hz).trans (hrow x z ((funext hxy).symm.trans hz)).symm
  have hlift : ∀ y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N),
      ∃ x : SplittingProjection.locLat v (SplittingProjection.dualLb L), ∀ i, y.1 i = SplittingProjection.prP s (x.1 i) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 (hpart1.le y.2)
    exact ⟨⟨x, hx⟩, fun i => (congrFun hxy i).symm⟩
  have hf0 : f ≠ 0 := (hf.ne_zero_iff hb).2 hφ
  have hsm : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = SplittingProjection.prP s a →
      ∀ (x : SplittingProjection.locLat v (SplittingProjection.dualLb L))
      (y : SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)),
      (∀ i, y.1 i = SplittingProjection.prP s (x.1 i)) → f (a' • y) = ε (L.fT v hv (a • x)) := by
    intro a a' ha x y hxy
    refine hfe _ _ fun i => ?_
    show (a' : v.adicCompletion F) * y.1 i = SplittingProjection.prP s ((a : E ⊗[F] v.adicCompletion F) * x.1 i)
    rw [map_mul, ha, hxy]
  refine ⟨s, hs', fun x hx => hfac x (funext hx), ?_, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩,
    f, ε, ?_, hfe, hf0, ?_, ?_, ?_⟩
  · rw [← (map_primes hs).1, ← (map_primes hs).2]
    exact ⟨iso⟩
  · intro a a' ha m
    obtain ⟨y, hy⟩ := surjective_of_ne_zero hf0 (ε m)
    obtain ⟨x, hx⟩ := hlift y
    have hm : m = L.fT v hv x := ε.injective (hy.symm.trans (hfe x y hx))
    rw [← hy, ← map_smul, hsm a a' ha x y hx, hm, (L.fT v hv).map_smul]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hsm (A.T : intV E v) (A.T : v.adicCompletionIntegers F) (by simp) x y hx, L.fT_T, map_zero]
  · intro y
    obtain ⟨x, hx⟩ := hlift y
    rw [hfe x y hx, map_eq_zero_iff _ ε.injective, hker x, ← SetLike.mem_coe, coe_partOf_prP hs',
      show y.1 = OverPlaceIntegralForm.pr₁ s x.1 from funext hx]
  · intro g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)

theorem overAt_of_localAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (hN : N ≤ SplittingProjection.dualLb L)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal)
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (H : SplittingProjection.LocalAtT L N v hv s) : OverPlaceIntegralForm.OverAt L N v hv := by
  obtain ⟨hs', hfac, ⟨iso⟩, hpart1, hpart2, huniq, hstab, ⟨b, hb, hlev⟩, f, ε, -, hfe, hf0, -, hker,
    hU⟩ := H
  replace hb : IsFrame (SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N)) b := hb
  obtain ⟨P, Pb, hs⟩ := exists_primes sp.cm.deg2 hs'
  obtain ⟨φ, hf⟩ := hb.exists_row f
  have hle : OverPlaceIntegralForm.latV v N ≤ OverPlaceIntegralForm.latV v (OverPlaceIntegralForm.baseDual L) :=
    Submodule.span_mono (Set.image_mono hN)
  have hmem : ∀ x : SplittingProjection.locLat v (SplittingProjection.dualLb L),
      OverPlaceIntegralForm.pr₁ s x.1 ∈ SplittingProjection.partOf (SplittingProjection.prP s) (SplittingProjection.locLat v N) := fun x => by
    rw [hpart1]
    exact Submodule.subset_span ⟨x.1, x.2, rfl⟩
  refine ⟨P, Pb, s, hs, fun x hx => hfac x (congrFun hx), ?_, ?_, ?_, ?_, ⟨hle, ?_, ?_⟩, b, φ, ε,
    ?_, ⟨?_, ?_, ?_⟩, (hf.ne_zero_iff hb).1 hf0, ?_, ?_⟩
  · intro x
    rw [← coe_partOf_prP hs', SetLike.mem_coe, ← map_eq_zero_iff _ ε.injective,
      ← hfe x ⟨_, hmem x⟩ (fun _ => rfl)]
    exact hker _
  · rw [(map_primes hs).1, (map_primes hs).2]
    exact ⟨iso⟩
  · rw [← coe_partOf_prP hs', ← coe_partOf_prP hs', hpart1]
  · rw [← coe_partOf_prPbar hs', ← coe_partOf_prPbar hs', hpart2]
  · intro h0
    apply hf0
    ext y
    obtain ⟨x, hx, hxy⟩ := (mem_partOf _ (sur_prP hs') _ y.1).1 y.2
    have h1 := hfe (Submodule.inclusion hle ⟨x, hx⟩) y (fun i => (congrFun hxy i).symm)
    have h2 : L.fT v hv (Submodule.inclusion hle ⟨x, hx⟩) = 0 := LinearMap.congr_fun h0 ⟨x, hx⟩
    rw [h1, h2, map_zero, LinearMap.zero_apply]
  · ext g
    rw [hU, Subgroup.mem_inf]
    refine and_congr_right fun hg => ?_
    exact (mem_stabFun_iff_part (SplittingProjection.prP s) _ _ (mem_partOf _ (sur_prP hs') _) _ f ε
      (fun x y hxy => hfe (Submodule.inclusion hle x) y hxy) g hg.2 ((hstab g hg.1).1 hg)).symm
  · exact (coe_partOf_prP hs' _).symm.trans ((isFrame_iff _ _).1 hb)
  · exact fun g hg => (hlev g hg.1).1 hg
  · intro g hg g' hg' hgg
    have h1 : bc (SplittingProjection.prP s) g = bc (SplittingProjection.prP s) g' :=
      mul_left_cancel (mul_right_cancel (show b⁻¹ * bc (SplittingProjection.prP s) g * b =
        b⁻¹ * bc (SplittingProjection.prP s) g' * b from hgg))
    have h2 : (⟨g, hg.1⟩ : UPts sp.cm.sig sp.gram0 (v.adicCompletion F)) = ⟨g', hg'.1⟩ :=
      (huniq (bc (SplittingProjection.prP s) g')).unique h1 rfl
    exact congrArg Subtype.val h2
  · intro u hu
    obtain ⟨g, hg, -⟩ := huniq (b * u * b⁻¹)
    have h1 : b⁻¹ * bc (SplittingProjection.prP s) g.1 * b = u := by rw [hg]; group
    exact ⟨g.1, (hlev g.1 g.2).2 (h1 ▸ hu), h1⟩
  · intro x y hxy
    exact (hfe x ⟨_, hmem x⟩ (fun _ => rfl)).symm.trans (hf _ y hxy)
  · intro g hg
    refine (hU g).trans (Iff.trans ⟨fun h => h.2, fun h => ⟨(hstab g hg).2 h.1, h⟩⟩ ?_)
    exact hf.mem_stabFun_iff hb _

theorem isOverLattice_iff (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) :
    OverPlaceIntegralForm.IsOverLattice L N ↔
      (SplittingProjection.IsOverLattice L N ∧
        (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal),
          ∃ φ, SplittingProjection.LocalAtT L N v h φ) ∧
        (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
        L.U ≤ levelAfL sp.cm.sig sp.gram0 N) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨h1, h2, h3, h4, fun x hx => Submodule.subset_span (h5 hx), h6⟩,
      fun v hv => localAtT_of_overAt L N v hv (h7 v hv), fun v => ?_, h8⟩
    by_cases hv : (A.T : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨P, Pb, s, -, -, -, -, -, -, ⟨hle, -, hU⟩, -⟩ := h7 v hv
      rw [hU]; exact inf_le_left
    · have : levelVL sp.cm.sig sp.gram0 v N = levelVL sp.cm.sig sp.gram0 v L.Lb :=
        congrArg (level _ _) (h6 v hv)
      rw [this]; exact L.Uloc_lev v
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, -, h8⟩
    refine ⟨h1, h2, h3, h4, fun y hy x hx => ?_, h6, fun v hv => ?_, h8⟩
    · rw [← h3] at hy
      exact hy x (h4 hx)
    · obtain ⟨s, hs⟩ := h7 v hv
      exact overAt_of_localAtT L N h5 v hv s hs

theorem overLatticeAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    OverPlaceIntegralForm.OverLatticeAt D Lv u ↔
      (letI := D.host.cmStar
       Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → SplittingProjection.HasOverLattice (Lv u)) := by
  letI := D.host.cmStar
  exact imp_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun N => isOverLattice_iff (Lv u) N

theorem overLattice_iff_selfDualOverBase : OverPlaceIntegralForm.OverLattice ↔ SplittingProjection.SelfDualOverBase :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => overLatticeAt_iff D Lv u

end GlobalTheory.OverCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParahoricLeIntegralGl
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.parahoric_le_integral_gl

theorem inX_mem_nfLat_iff {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n c : ℕ)
    (e : Fin c → ℤ) (z : Sp E n) (x : Sp E n) :
    Loc.inX E n c x ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z ↔ x ∈ stdAt E n P := by
  constructor
  · rintro ⟨l, hl, s, -, h⟩
    have hs : ∀ b, s b = 0 := by
      intro b
      have h1 := congrFun h (Fin.natAdd n b)
      have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
      have h2 : ∀ (y : Fin n → E), Loc.inX E n c y (Fin.natAdd n b) = 0 := fun y => by
        rw [inX_apply, dite_eq_right (by simp)]
      have h3 : ∀ i : Fin c, IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen (qOf P) n c e z i (Fin.natAdd n b) =
          if b = i then ((qOf P : E) ^ e i) else 0 := by
        intro i
        unfold IndefiniteRowSideFullHecke.SandwichNormalForm.nfGen
        rw [Pi.smul_apply, Pi.add_apply]
        have h4 : (if i.1 = 0 then Loc.inX E n c z else 0 : Sp E (n + c)) (Fin.natAdd n b) = 0 := by
          split_ifs
          · exact h2 z
          · rfl
        rw [h4]
        simp [Loc.eN, Fin.val_inj]
      rw [Pi.add_apply, h2, h2, Finset.sum_apply] at h1
      simp only [Pi.smul_apply, h3, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, zero_add] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_right (zpow_ne_zero _ hq)
    simp only [hs, zero_smul, Finset.sum_const_zero, add_zero] at h
    rwa [inX_injective h]
  · intro hx
    exact ⟨x, hx, 0, fun _ => IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P, by simp⟩

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P h → prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  rintro X Pr R sharp j P hP h ⟨e, z, -, -, hnf⟩ g ⟨r, ⟨-, hr⟩, hrg⟩ x
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) sharp j P := by
    have := Subgroup.mem_comap.1 hr
    simpa using this
  unfold Jat at hJ
  rw [if_neg hP] at hJ
  have hk := hJ.1
  have key : ∀ y, y ∈ IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z ↔ h⁻¹ y ∈ stdAt X.E _ P := by
    intro y
    rw [← hnf, mem_stdAt_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : h⁻¹ (h w) = w := h.symm_apply_apply w
      rw [this]
      exact (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP w).1 hw
    · intro hy
      exact ⟨h⁻¹ y, (IndefiniteRowSideFullHecke.SandwichNormalForm.mem_lamYat hP _).2 hy, h.apply_symm_apply y⟩
  rw [← inX_mem_nfLat_iff P _ (cOf R j) e z, ← inX_mem_nfLat_iff P _ (cOf R j) e z, ← hrg, key, key,
    ← hk (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x))]
  have : (h⁻¹ * r * h) (h⁻¹ (Loc.inX X.E (R.N j) (cOf R j) x)) = h⁻¹ (r (Loc.inX X.E (R.N j) (cOf R j) x)) := by
    change h⁻¹ (r (h (h.symm _))) = _
    rw [h.apply_symm_apply]
  rw [this]

end GlobalTheory.Proof.parahoric_le_integral_gl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalFractionsRepresentPrimeNormQuotient
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient

open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.Proof.IntegralPowerExpansion

variable {E : Type} [Field E] [NumberField E]

theorem intAt_int (P : HeightOneSpectrum (𝓞 E)) (n : ℤ) : IntAt P (n : E) := by
  simpa using IntAt.coe P (n : 𝓞 E)

theorem q_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) {n : ℤ}
    (h : IntAt P ((qOf P : E)⁻¹ * n)) : (qOf P : ℤ) ∣ n := by
  by_contra hn
  have hpr : Prime (qOf P : ℤ) := Nat.prime_iff_prime_int.1 hP.1
  obtain ⟨x, y, hxy⟩ := (hpr.coprime_iff_not_dvd).2 hn
  have hq := q_ne_zero hP
  have h1 : IntAt P ((qOf P : E)⁻¹) := by
    have e : (qOf P : E)⁻¹ = x + y * ((qOf P : E)⁻¹ * n) := by
      have := congrArg (Int.cast : ℤ → E) hxy
      push_cast at this
      field_simp
      linear_combination -this
    rw [e]
    exact (intAt_int P x).add ((intAt_int P y).mul h)
  rw [intAt_iff_val, map_inv₀, val_q hP, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem q_pow_dvd_of_intAt {P : HeightOneSpectrum (𝓞 E)} (hP : DegOneUnram P) (k : ℕ) {n : ℤ}
    (h : IntAt P (((qOf P : E) ^ k)⁻¹ * n)) : (qOf P : ℤ) ^ k ∣ n := by
  have hq := q_ne_zero hP
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h1 : IntAt P ((qOf P : E)⁻¹ * n) := by
      have e : (qOf P : E)⁻¹ * n = (((qOf P : ℤ) ^ k : ℤ) : E) * (((qOf P : E) ^ (k + 1))⁻¹ * n) := by
        push_cast
        field_simp
        ring
      rw [e]
      exact (intAt_int P _).mul h
    obtain ⟨m, rfl⟩ := q_dvd_of_intAt hP h1
    have e : ((qOf P : E) ^ (k + 1))⁻¹ * (((qOf P : ℤ) * m : ℤ) : E) = ((qOf P : E) ^ k)⁻¹ * m := by
      push_cast
      field_simp
      ring
    rw [e] at h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih h)

theorem valsQ_reps : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ,
    (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B,
      IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧
    ∀ a : E, IntAt P ((qOf P : E) ^ A * a) →
      ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s)) := by
  intro E _ _ P hP A B
  classical
  have hq := q_ne_zero hP
  constructor
  · intro a ha b hb h
    unfold LocE.valsQ at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_range] at hi hj
    have h1 : IntAt P (((qOf P : E) ^ (A + B))⁻¹ * (((i : ℤ) - j : ℤ) : E)) := by
      convert h using 1
      push_cast
      field_simp
      ring
    have h2 := q_pow_dvd_of_intAt hP _ h1
    have hi' : (i : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hi
    have hj' : (j : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast hj
    have h3 : (i : ℤ) - j = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
    have h4 : i = j := by omega
    rw [h4]
  · intro a ha
    obtain ⟨k, u, hu, e⟩ := exists_int_add_q_pow_mul hP (A + B) ha
    have hpos : (0 : ℤ) < (qOf P : ℤ) ^ (A + B) := by exact_mod_cast pow_pos hP.1.pos (A + B)
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg k hpos.ne')
    have hlt : i < qOf P ^ (A + B) := by
      have := Int.emod_lt_of_pos k hpos
      rw [hi] at this
      exact_mod_cast this
    have hk : (k : E) = i + (qOf P : E) ^ (A + B) * ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) := by
      have := Int.emod_add_mul_ediv k ((qOf P : ℤ) ^ (A + B))
      rw [hi] at this
      have h5 := congrArg (Int.cast : ℤ → E) this
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_natCast] at h5
      exact h5.symm
    unfold LocE.valsQ
    refine ⟨_, Finset.mem_image.2 ⟨i, Finset.mem_range.2 hlt, rfl⟩, ?_⟩
    have h6 := (intAt_int P (k / (qOf P : ℤ) ^ (A + B))).add hu
    generalize ((k / (qOf P : ℤ) ^ (A + B) : ℤ) : E) = m at hk h6
    have ea : a = ((qOf P : E) ^ A)⁻¹ * (i + (qOf P : E) ^ (A + B) * (m + u)) := by
      rw [eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hq), e, hk]
      ring
    convert h6 using 1
    rw [ea]
    field_simp
    ring

end GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingBoundedIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.unfolding_bounded_integral

section SlopeTestRemainingChoices

variable {F : Type} [Field F] {n' c' n c : ℕ}

def extZ (c' c : ℕ) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F) :=
  Loc.inX F n c ∘ₗ z ∘ₗ LinearMap.funLeft F F (Fin.castAdd c')

theorem extZ_apply (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (v : Fin (n' + c') → F) :
    extZ c' c z v = Loc.inX F n c (z fun a => v (Fin.castAdd c' a)) := rfl

theorem unfoldingAffineLinearMap_add_eq_add_frM (xj z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) (t : Loc.FC n' c' n c → F) :
    Loc.xx1 (xj + a • z) t = Loc.xx1 xj t + a • extZ c' c z := by
  refine LinearMap.pi_ext' fun s => LinearMap.ext_ring ?_
  funext l
  change Loc.xx1 (xj + a • z) t (Pi.single s 1) l =
    Loc.xx1 xj t (Pi.single s 1) l + a * extZ c' c z (Pi.single s 1) l
  rw [linearMap_unfolding_apply_single, linearMap_unfolding_apply_single, extZ_apply, inX_apply]
  by_cases hs : s.1 < n'
  · have hf : ¬ Loc.IsFree n' n c l.1 s.1 := fun h => by have := h.1; omega
    have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) =
        Pi.single (⟨s.1, hs⟩ : Fin n') 1 := by
      funext b
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    rw [dite_eq_right hf, dite_eq_right hf, dite_eq_left hs, dite_eq_left hs, e]
    split_ifs with hl
    · simp
    · simp
  · have e : (fun b : Fin n' => (Pi.single s (1 : F) : Fin (n' + c') → F) (Fin.castAdd c' b)) = 0 := by
      funext b
      have := b.2
      rw [Pi.single_apply, if_neg]
      · rfl
      · intro h
        apply hs
        rw [← h]
        simp
    rw [e, map_zero, dite_eq_right hs, dite_eq_right hs]
    simp

theorem chArg_add (x : (Fin (n' + c') → F) →ₗ[F] (Fin (n + c) → F)) (z : (Fin n' → F) →ₗ[F] (Fin n → F)) (a : F) :
    Loc.chArg (x + a • extZ c' c z) = Loc.chArg x := by
  unfold Loc.chArg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul, extZ_apply,
    atN_of_mem_Ufl (inX_mem_Ufl i _), mul_zero, add_zero]

end SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

theorem intV_inX {P : HeightOneSpectrum (𝓞 E)} {n c : ℕ} {v : Fin n → E} (hv : IntV P v) : IntV P (Loc.inX E n c v) := by
  intro l
  rw [inX_apply]
  split_ifs
  · exact hv _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfold_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (N A B : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), HomBdd P N Psi → (∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj ≠ 0 → IntHom P (((qOf P : E) ^ N) • xj)) ∧ ∀ xj z : (Fin n' → E) →ₗ[E] (Fin n → E), IntHom P z → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi (xj + ((qOf P : E) ^ N) • z) = GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB P psi A B Psi xj := by
  intro E _ _ K _ P n' c' n c psi N A B Psi hPsi
  refine ⟨fun xj hx => ?_, fun xj z hz => ?_⟩
  · unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1 at hx
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    have h := hPsi.1 _ (left_ne_zero_of_mul ht)
    intro v hv a
    have h2 := h _ (intV_inX (c := c') hv) (Fin.castAdd c a)
    rw [LinearMap.smul_apply, unfoldingAffinePointMap_apply_inclusion, Pi.smul_apply, inX_castAdd] at h2
    exact h2
  · have hy : IntHom P (extZ c' c z) := fun v hv => by
      rw [extZ_apply]
      exact intV_inX (hz _ fun a => hv _)
    unfold IndefiniteRowSideFullHecke.SourceLatticeInvariance.unfoldAB Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [unfoldingAffineLinearMap_add_eq_add_frM, chArg_add, hPsi.2 _ _ hy]

end GlobalTheory.Proof.unfolding_bounded_integral
end
end

