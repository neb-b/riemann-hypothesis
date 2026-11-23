module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoordsDetermineFamily
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.CoordFamily

open Filter Topology GlobalTheory.Specialise GlobalTheory.AmpleSpan GlobalTheory.HolHom

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {H : LB X} {I : Type} {t : I → LB.Sec H}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V → (Sp ℂ ⟶ X)} {cf : I → V → ℂ}

theorem eq_of_proportional (ht : EmbedsBy f t) {p p' : Sp ℂ ⟶ X} (hf : p ≫ f = p' ≫ f) {c c' : I → ℂ}
    (h : HasCoords p t c) (h' : HasCoords p' t c') {ρ : ℂ} (e : ∀ i, c' i = ρ * c i) : p = p' := by
  obtain ⟨m, hm⟩ := h'.exists_isUnit ht.1
  have hρ : IsUnit ρ := isUnit_of_mul_isUnit_left (e m ▸ hm)
  have h₁ := h.mul_unit hρ
  have e' : (fun l => c l * ρ) = c' := funext fun l => by rw [e, mul_comm]
  rw [e'] at h₁
  exact h₁.ext ht hf h' hm

theorem holAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z) : HolAt x z := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit ht.1
  obtain ⟨hD, ρ, hρ, hsurj⟩ := ht.2 m
  have hne : ∀ᶠ v in 𝓝 z, cf m v ≠ 0 := (hd m).continuousAt.eventually_ne hm.ne_zero
  have hev : ∀ᶠ v in 𝓝 z, ⊤ ≤ x v ⁻¹ᵁ Out.nonzeroLocus (t m) :=
    hne.mono fun v hv => (hc v).le_nonzeroLocus hv.isUnit
  refine holAt_of_affine hD hev.self_of_nhds hev fun g => ?_
  obtain ⟨q, rfl⟩ := hsurj g
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine (differentiableAt_const (valR y ⊤ a)).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [MvPolynomial.eval₂Hom_C, valAt'_eq_valR]
    exact (HolHom.valR_appLE (x v) f ⊤ _ le_top a hv).trans (by rw [hy])
  | add p q hp hq =>
    refine (hp.add hq).congr_of_eventuallyEq (hev.mono fun v hv => ?_)
    simp only [valAt'_eq_valR, HolHom.valR_eq _ _ hv, map_add (f := _), Pi.add_apply]
  | mul_X p l hp =>
    refine (hp.mul ((hd l).fun_mul ((hd m).fun_inv hm.ne_zero))).congr_of_eventuallyEq
      ((hev.and hne).mono fun v hv => ?_)
    have e := (hc v).valR_ratio hv.1 (hρ l)
    have e' : valR (x v) _ (ρ l) = cf l v * (cf m v)⁻¹ := by
      rw [← e, mul_inv_cancel_right₀ hv.2]
    simp only [valAt'_eq_valR, map_mul, MvPolynomial.eval₂Hom_X', Pi.mul_apply]
    rw [← e']
    simp only [HolHom.valR_eq _ _ hv.1, map_mul]

theorem hasCoords_deriv (hcov : ⨆ l, Out.nonzeroLocus (t l) = ⊤) (hc : ∀ v, HasCoords (x v) t fun i => cf i v)
    {z w : V} (hx : HolAt x z) (hd : ∀ i, DifferentiableAt ℂ (cf i) z) {ν : Sp (DualNumber ℂ) ⟶ X}
    (hν : IsDerivAt x z w ν) :
    HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w) := by
  obtain ⟨m, hm⟩ := (hc z).exists_isUnit hcov
  choose ρ hρ using fun l => exists_isRatio (t l) (t m)
  have hz := (hc z).le_nonzeroLocus hm
  have hν' := (le_preimage_dual_iff hν.1 _).2 hz
  have hu : IsUnit (TrivSqZeroExt.inl (cf m z) + TrivSqZeroExt.inr (fderiv ℂ (cf m) z w) : DualNumber ℂ) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by simpa using hm)
  have h₁ := (hasCoords_ratio hν' hρ).mul_unit hu
  convert h₁ using 2 with l
  have hev : cf l =ᶠ[𝓝 z] fun v => valAt' (x v) _ (ρ l) * cf m v :=
    (hx _ hz).1.mono fun v hv => ((hc v).valR_ratio hv (hρ l)).symm
  have h0 := hev.self_of_nhds
  beta_reduce at h0
  rw [hev.fderiv_eq, h0, fderiv_fun_mul ((hx _ hz).2 _) (hd m)]
  ext
  · simp [fst_valR hν.1 hz]
  · simp [fst_valR hν.1 hz, hν.2 _ hz, mul_comm]

theorem isDerivAt_of_coords (ht : EmbedsBy f t) {y : Sp ℂ ⟶ Y} (hy : ∀ v, x v ≫ f = y)
    (hc : ∀ v, HasCoords (x v) t fun i => cf i v) {z w : V} (hd : ∀ i, DifferentiableAt ℂ (cf i) z)
    {ν : Sp (DualNumber ℂ) ⟶ X} (hb : ν ≫ f = constVec y)
    (hν : HasCoords ν t fun i => TrivSqZeroExt.inl (cf i z) + TrivSqZeroExt.inr (fderiv ℂ (cf i) z w)) :
    IsDerivAt x z w ν := by
  have hx := holAt_of_coords ht hy hc hd
  obtain ⟨ν', hν'⟩ := hx.exists_isDerivAt w
  have h1 := hν'.comp f
  have h2 : (fun v => x v ≫ f) = fun _ => y := funext hy
  have h3 : ν' ≫ f = constVec y := (h2 ▸ h1).unique (isDerivAt_const y z w)
  rw [hν.ext_of_isLocalRing ht (hb.trans h3.symm) (hasCoords_deriv ht.1 hc hx hd hν')]
  exact hν'

theorem hasCoords_powOver {S : Scheme.{0}} {G : Over S} {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {b : I → LB.Sec (Out.powOver G L U N)} {A : Type} [CommRing A] [IsLocalRing A]
    {p : Sp A ⟶ (G.hom ⁻¹ᵁ U).toScheme} {c : I → A}
    (h : ∀ j, ⊤ ≤ (p ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : Aˣ,
      ∀ i, valR p ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = c i * u) : HasCoords p b c := by
  obtain ⟨j, hj⟩ := Points.exists_le_preimage_of_iSup_eq_top (p ≫ (G.hom ⁻¹ᵁ U).ι) hL.cover
  exact ⟨fun _ => j, fun s hs => Set.mem_iInter.2 fun _ => hj hs, h j hj⟩

end GlobalTheory.CoordFamily

namespace GlobalTheory


open Specialise HolHom CoordFamily in
theorem coords_determine_family : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (y : Sp ℂ ⟶ S) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (x : V → (Sp ℂ ⟶ (G.hom ⁻¹ᵁ U).toScheme)) (cf : Fin n → V → ℂ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → (∀ v, x v ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y) → (∀ v j, ⊤ ≤ (x v ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : ℂ, u ≠ 0 ∧ ∀ i, valR (x v) ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = cf i v * u) → (∀ v v' (ρ : ℂ), (∀ i, cf i v' = ρ * cf i v) → x v' = x v) ∧ ((∀ i, Differentiable ℂ (cf i)) → IsHolTo Set.univ (fun v => x v ≫ (G.hom ⁻¹ᵁ U).ι) ∧ ∀ (z₀ : V) (ν : Sp (DualNumber ℂ) ⟶ (G.hom ⁻¹ᵁ U).toScheme), ν ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y → (∀ j, ⊤ ≤ (ν ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → ∃ u : (DualNumber ℂ)ˣ, ∀ i, valR ν ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = (TrivSqZeroExt.inl (cf i 0) + TrivSqZeroExt.inr (fderiv ℂ (cf i) 0 z₀)) * (u : DualNumber ℂ)) → ∀ (W : G.left.Opens) (f : Γ(G.left, W)), spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ ν = x 0 ∧ (⊤ ≤ (x 0 ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (ν ≫ (G.hom ⁻¹ᵁ U).ι) W f) = fderiv ℂ (fun v => valAt' (x v ≫ (G.hom ⁻¹ᵁ U).ι) W f) 0 z₀)) := by
  intro S G _ L U N n b y V _ _ x cf hL _ hb hy hc
  have hc' : ∀ v, HasCoords (x v) b fun i => cf i v := fun v => hasCoords_powOver hL fun j hj => by
    obtain ⟨u, hu, e⟩ := hc v j hj
    exact ⟨Units.mk0 u hu, e⟩
  have hi : (G.hom ∣_ U) ≫ U.ι = (G.hom ⁻¹ᵁ U).ι ≫ G.hom := morphismRestrict_ι _ _
  have hy' : ∀ v, x v ≫ (G.hom ∣_ U) = x 0 ≫ (G.hom ∣_ U) := fun v => by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hi, hy, hy]
  refine ⟨fun v v' ρ e => (eq_of_proportional hb ((hy' v).trans (hy' v').symm) (hc' v) (hc' v') e).symm,
    fun hd => ⟨isHolTo_of_holAt isOpen_univ fun z _ => (holAt_of_coords hb hy' hc' fun i => hd i z).comp _,
      fun z₀ ν hν hνc W f => ?_⟩⟩
  have h := isDerivAt_of_coords (w := z₀) hb hy' hc' (fun i => hd i 0) (ν := ν)
    (by rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hi, hν, hy])
    (hasCoords_powOver hL hνc)
  exact ⟨h.1, fun hW => (h.comp (G.hom ⁻¹ᵁ U).ι).2 W hW f⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsBasisFSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory

theorem AnArc.FSum_sum_smul {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (j : ℕ) [NeZero j] (α : A.X)
    {K : Type} (s : Finset K) (c : K → ℂ) (th : K → (Fin A.gB → ℂ) → ℂ) (v : A.V) :
    A.FSum j α (∑ i ∈ s, c i • th i) v = ∑ i ∈ s, HahnSeries.single 0 (c i) * A.FSum j α (th i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := A.FSum_smul j α 0 0 v
    rw [zero_smul, zero_smul] at h
    simpa using h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, A.FSum_add, ih, A.FSum_smul,
      HahnSeries.single_zero_mul_eq_smul]

theorem AnArc.exists_basis_FSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A → ∀ (j : ℕ) [NeZero j], ∃ (n : ℕ) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ) (T₀ : ℝ), (∀ i, th i ∈ A.Theta j (α i)) ∧ LinearIndependent ℂ⸨X⸩ (fun i v => A.FSum j (α i) (th i) v) ∧ (∀ w : ℂ, T₀ < w.im → LinearIndependent ℂ (fun i v => A.Sum j (α i) (th i) w v)) ∧ ∀ α', ∀ th' ∈ A.Theta j α', ∃ r : Fin n → ℂ⸨X⸩, (∀ i T, r i ∈ Conv.halfRing T) ∧ ∀ v, A.FSum j α' th' v = ∑ i, r i * A.FSum j (α i) (th i) v := by
  intro O _ _ A hA j _
  classical
  have hj : 1 ≤ j := Nat.one_le_iff_ne_zero.2 (NeZero.ne j)
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul A.X j hj
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  have : ∀ c, Module.Finite ℂ (A.Theta j (e c)) := fun c => hA.1 j (e c) hj
  let b := fun c => Module.finBasis ℂ (A.Theta j (e c))
  let I := fun c => Fin (Module.finrank ℂ (A.Theta j (e c)))
  let t : ∀ c, I c → (Fin A.gB → ℂ) → ℂ := fun c i => b c i
  have ht : ∀ c, LinearIndependent ℂ (t c) := fun c =>
    (b c).linearIndependent.map' (A.Theta j (e c)).subtype (Submodule.ker_subtype _)
  have htm : ∀ c i, t c i ∈ A.Theta j (e c) := fun c i => (b c i).2
  have hrep : ∀ c c' y, e c = e c' + j • y → c = c' := fun c c' y h =>
    (he (e c)).unique ⟨0, by simp⟩ ⟨y, h⟩
  let s := (Fintype.equivFin (Σ c, I c)).symm
  refine ⟨_, fun i => e (s i).1, fun i => t (s i).1 (s i).2, T₀, fun i => htm _ _,
    (A.linearIndependent_FSum_sigma hrep ht).comp s s.injective, fun w hw =>
    (A.linearIndependent_Sum_sigma (NeZero.ne j) hrep ht w fun c i z =>
      AnArc.summable_term hT (NeZero.ne j) (htm c i) hw (0, z)).comp s s.injective, fun α' th' hth' => ?_⟩
  obtain ⟨c, ⟨m, hm⟩, -⟩ := he α'
  have hα : α' + j • (-m) = e c := by rw [hm]; simp
  have hmem := A.translate_mem_Theta hth' (-m)
  rw [hα] at hmem
  let x := (b c).repr ⟨_, hmem⟩
  have hx : (fun z => th' (z + A.ct (-m))) = ∑ i, x i • t c i := by
    have := congrArg Subtype.val ((b c).sum_repr ⟨_, hmem⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  let u : ℂ⸨X⸩ := HahnSeries.single (A.exponent j α' (-m)) ((A.psi (-m) : ℂ) ^ j * eTwoPi (A.T (-m) α'))
  obtain ⟨r, hr1, hr0⟩ : ∃ r : ∀ c', I c' → ℂ⸨X⸩, (∀ i, r c i = u * HahnSeries.single 0 (x i)) ∧
      ∀ c', c' ≠ c → ∀ i, r c' i = 0 :=
    ⟨Pi.single (M := fun c' => I c' → ℂ⸨X⸩) c fun i => u * HahnSeries.single 0 (x i),
      fun i => by rw [Pi.single_eq_same], fun c' h i => by rw [Pi.single_eq_of_ne h]; rfl⟩
  refine ⟨fun i => r (s i).1 (s i).2, fun i T => ?_, fun v => ?_⟩
  · beta_reduce
    generalize s i = p
    obtain ⟨c', i'⟩ := p
    by_cases h : c' = c
    · subst h
      rw [hr1]
      exact mul_mem (Conv.single_mem_halfRing _ _ _) (Conv.single_mem_halfRing _ _ _)
    · rw [hr0 c' h]
      exact zero_mem _
  · rw [s.sum_comp (fun p : Σ c, I c => r p.1 p.2 * A.FSum j (e p.1) (t p.1 p.2) v), Fintype.sum_sigma,
      Finset.sum_eq_single c (fun c' _ h => by simp [hr0 c' h]) (by simp),
      A.FSum_eq_translate j α' th' (-m) v, hα, hx, A.FSum_sum_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hr1, _root_.mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCharacterRatioExpMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbelianLetters

theorem exists_ratio_valR {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {ε : K → ℤ} (hL : L.IsLB) {φ φ' : K → (Sp A ⟶ X)} (e : φ = φ') (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ a : Γ(Sp A, ⊤)ˣ, (∀ z J, Good L z J → val t (𝟙 _) z J = gm (𝟙 _) z ⊤ a * val t' (𝟙 _) z J) ∧
      ∀ j, ⊤ ≤ LB.wchart L φ j → valR (𝟙 (Sp A)) (LB.wchart L φ j) (t.s j).val =
        valR (𝟙 (Sp A)) ⊤ a.val * valR (𝟙 (Sp A)) (LB.wchart L φ' j) (t'.s j).val := by
  subst e
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL (fun _ _ _ => rfl) t ht t' ht'
  refine ⟨a, fun z J hJ => ha _ _ z J hJ, fun j hj => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hL (cpt A)
  have toStkA_valR {B : Type} [CommRing B] {Y : Scheme.{0}} (x : Sp B ⟶ Y)
      (U : Y.Opens) (z : Sp B) (ht : ⊤ ≤ x ⁻¹ᵁ U) (b : Γ(Y, U)ˣ) :
      toStkA z (valR x U b.val) = (gm x z U b).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp B).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c)
        (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of B)))
    rw [valR, dite_eq_left ht, gm, dite_eq_left hz]
    show ((Sp B).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE U ⊤ ht).hom b.val))) =
      ((Sp B).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom b.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp B).presheaf (homOfLE ht) z trivial ((x.app U).hom b.val)
  apply toStkA_injective
  have hm : (𝟙 (Sp A) : Sp A ⟶ Sp A) (cpt A) ∈ LB.wchart L φ j := hj (x := cpt A) trivial
  rw [map_mul, toStkA_valR _ ⊤ _ le_rfl, toStkA_valR _ (LB.wchart L φ j) _ hj (t.s j),
    toStkA_valR _ (LB.wchart L φ j) _ hj (t'.s j), ← Units.val_mul,
    gen_trans ht _ _ hm (hJ.mem φ _), gen_trans ht' _ _ hm (hJ.mem φ _), mul_left_comm]
  exact congrArg (fun q => Units.val (_ * q)) (ha _ _ _ J hJ)

theorem exists_isRatio_mul [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ)
    (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt)
    (hb : ∀ Tt b, (sB Tt b).b = b ^ n)
    (hadd : ∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b')))
    (hpull : ∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b)))
    (hex : ∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) :
    ∃ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u ∧ (∀ x z, u x z ≠ 0) ∧
      ∀ x z z', u x (z + z') = u x z * u x z' := by
  have eb : ∀ z, (ex ((n : ℂ) • z)).b = (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b := fun z => by
    rw [b_nsmul hex, hb]
  choose a ha hv using fun x z => exists_ratio_valR (A := ℂ) D.P.isLB
    (φ := Out.DegPre.gtφ D ℂ (ex ((n : ℂ) • z)).b x)
    (φ' := Out.DegPre.gtφT D (Out.TF (R := ℂ) ℂ) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b x)
    (by rw [eb]; rfl) ((ex ((n : ℂ) • z)).s x) ((sB (Out.TF (R := ℂ) ℂ) (ex z).b).s x)
    ((ex _).isGen x) ((sB _ _).isGen x)
  have hev : ∀ c : Γ(Sp ℂ, ⊤), valR (𝟙 (Sp ℂ)) ⊤ c = HolHom.evalHom (𝟙 (Sp ℂ)) ⊤ le_rfl c := fun c =>
    HolHom.valR_eq _ _ _ c
  refine ⟨fun x z => valR (𝟙 (Sp ℂ)) ⊤ (a x z).val, fun x z j hj => ?_, fun x z => ?_, fun x z z' => ?_⟩
  · refine (hv x z j hj).trans (congrArg (_ * ·) ?_)
    have H := hpull D.P.A _ (ex z).b (𝟙 _)
    rw [Category.comp_id] at H
    exact valR_of_isPull H x j
  · exact (hev _).trans_ne ((a x z).isUnit.map _).ne_zero
  · have : a x (z + z') = a x z * a x z' := unit_ext fun w _ => by
      obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB w
      have e1 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hex ((n : ℂ) • z) ((n : ℂ) • z')).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e2 := (val_mul hJ _ _ _).symm.trans
        ((val_corr hJ ((hadd _ (ex z).b (ex z').b).2 x) (𝟙 _)).trans (val_mul hJ _ _ _))
      have e3 : val (Out.DegPre.cubAt D ℂ (Out.DegPre.cF D ℂ x) (ex ((n : ℂ) • z)).b (ex ((n : ℂ) • z')).b) (𝟙 _) w J =
          val (Out.DegPre.cubAtT D _ (Out.DegPre.cT D _ x) (sB (Out.TF (R := ℂ) ℂ) (ex z).b).b
            (sB (Out.TF (R := ℂ) ℂ) (ex z').b).b) (𝟙 _) w J := by
        rw [eb, eb]; rfl
      rw [← smul_add] at e1
      rw [← b_add hex] at e2
      have key : ∀ {U : Type} [CommGroup U] {p q r c c' p' q' r' k₁ k₂ k₃ : U}, r * c = p * q → r' * c' = p' * q' →
          c = c' → p = k₁ * p' → q = k₂ * q' → r = k₃ * r' → k₃ = k₁ * k₂ := by
        intro U _ p q r c c' p' q' r' k₁ k₂ k₃ h₁ h₂ h₃ h₄ h₅ h₆
        rw [h₃, h₄, h₅, h₆, _root_.mul_assoc, h₂, _root_.mul_mul_mul_comm] at h₁
        exact mul_right_cancel h₁
      rw [map_mul]
      exact key e1 e2 e3 (ha x z w J hJ) (ha x z' w J hJ) (ha x (z + z') w J hJ)
    simp only [this, hev, Units.val_mul, map_mul]

end GlobalTheory.AbelianLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEntireUnitAppellHumbertFrameRatio
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.FrameCompare

open GlobalTheory.PullHermitian

section Val

variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) {L : LB Y} {L' : LB X} (φ : X ⟶ Y)

abbrev ix (j : L.ι) (i : L'.ι) : (LB.div (L.pull φ) L').ι := (fun _ => j, i)

lemma ix_chart (j : L.ι) (i : L'.ι) (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (L.pull φ) L').U (ix φ j i) :=
  inf_of x (wchart_of x L φ j hj) hi

lemma val_iso_pull (w : LB.Iso L' (L.pull φ)) (hw : w.IsGen) (j j' : L.ι) (i i' : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j')
    (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ L'.U i') :
    valAt' x _ (w.s (ix φ j i)).val * valAt' x (L'.U i ⊓ L'.U i') (L'.g i i').val =
      valAt' (x ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * valAt' x _ (w.s (ix φ j' i')).val := by
  have c := wchart_of x L φ j hj
  have c' := wchart_of x L φ j' hj'
  have h := unitVal_iso x w hw (fun _ => j) (fun _ => j') i i' c c' hi hi'
  have h3 := unitVal_linComb x L φ 1 j j' (inf_of x c c') (inf_of _ hj hj')
  replace h := h.trans (congrArg (fun a => a * _ * _) h3)
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi),
    valAt'_eq_unitVal x (ix_chart x φ j' i' hj' hi'),
    valAt'_eq_unitVal x (inf_of x hi hi'), valAt'_eq_unitVal _ (inf_of _ hj hj')]
  have h4 := congrArg Units.val h
  simp only [Units.val_mul, zpow_one, Units.val_inv_eq_inv_val] at h4
  refine (congrArg (· * _) h4).trans ?_
  field_simp

lemma val_ne_zero (w : LB.Iso L' (L.pull φ)) (j : L.ι) (i : L'.ι)
    (hj : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U j) (hi : ⊤ ≤ x ⁻¹ᵁ L'.U i) :
    valAt' x _ (w.s (ix φ j i)).val ≠ 0 := by
  rw [valAt'_eq_unitVal x (ix_chart x φ j i hj hi)]
  exact Units.ne_zero _

end Val

theorem exists_entire_unit_automorphy :
    ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  intro A' _ X L L' hL hL' φ w hw g g' u Hm χ hu e F he fr th θ hd hne hc hθ
  obtain rfl : e = fun z => (u.ex (F z)).left ≫ φ := funext fun z => (he z).symm
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun p : L.ι × L'.ι => F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
    (fun p => ((u.hol _ 0).1.inter (u.hol _ 0).1).preimage hFd.continuous)
    (fun z => by
      obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
      obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
      exact ⟨(j, i), hj, hi⟩)
    (fun p z => fr p.1 z / (valAt' (u.ex (F z)).left _ (w.s (ix φ p.1 p.2)).val * u.fr p.2 (F z)))
    (fun p => by
      have d1 := (u.hol _ (w.s (ix φ p.1 p.2)).val).2.comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) hFd.differentiableOn
        fun z hz => ix_chart _ φ _ _ hz.1 hz.2
      have d2 := (u.fr_hol p.2).comp
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2}))
        hFd.differentiableOn fun z hz => hz.2
      have d3 := (hd p.1).mono
        (s := F ⁻¹' ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ L.U p.1)} ∩
          {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U p.2})) fun z hz => hz.1
      simp only [div_eq_mul_inv]
      exact d3.mul ((d1.mul d2).inv fun z hz =>
        mul_ne_zero (val_ne_zero _ φ w _ _ hz.1 hz.2) (u.fr_ne p.2 _ hz.2)))
    (fun p q z hp hq => by
      have h := val_iso_pull (u.ex (F z)).left φ w hw p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2
      have h1 := hc p.1 q.1 z (inf_of _ hp.1 hq.1)
      have h2 := u.fr_compat p.2 q.2 (F z) (inf_of _ hp.2 hq.2)
      rw [div_eq_div_iff (mul_ne_zero (val_ne_zero _ φ w _ _ hp.1 hp.2) (u.fr_ne _ _ hp.2))
        (mul_ne_zero (val_ne_zero _ φ w _ _ hq.1 hq.2) (u.fr_ne _ _ hq.2)),
        h1, h2, ← _root_.mul_assoc (valAt' _ _ (w.s (ix φ p.1 p.2)).val), h]
      ring)
  have hchart : ∀ z, ∃ j i, ⊤ ≤ ((u.ex (F z)).left ≫ φ) ⁻¹ᵁ L.U j ∧
      ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ L'.U i := fun z => by
    obtain ⟨j, hj⟩ := exists_chart ((u.ex (F z)).left ≫ φ) hL
    obtain ⟨i, hi⟩ := exists_chart (u.ex (F z)).left hL'
    exact ⟨j, i, hj, hi⟩
  refine ⟨r, hr, fun z => ?_, fun la l hl z => ?_⟩
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    rw [hrφ (j, i) z ⟨hj, hi⟩]
    exact div_ne_zero (hne _ _ hj) (mul_ne_zero (val_ne_zero _ φ w _ _ hj hi) (u.fr_ne _ _ hi))
  · obtain ⟨j, i, hj, hi⟩ := hchart z
    have hper : u.ex (F (z + la)) = u.ex (F z) := by
      rw [map_add (f := _), hl, u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
    have hj' : ⊤ ≤ ((u.ex (F (z + la))).left ≫ φ) ⁻¹ᵁ L.U j := by rwa [hper]
    have hi' : ⊤ ≤ (u.ex (F (z + la))).left ⁻¹ᵁ L'.U i := by rwa [hper]
    have h1 := hu.2.2.2 l i (F z) hi
    have t1 := hθ j z hj
    have t2 := hθ j (z + la) hj'
    have n1 := u.fr_ne _ _ hi
    have n2 := u.fr_ne _ _ hi'
    have n3 := val_ne_zero _ φ w _ _ hj hi
    rw [hrφ (j, i) z ⟨hj, hi⟩, hrφ (j, i) (z + la) ⟨hj', hi'⟩]
    simp only [hper] at t2 ⊢
    rw [← mul_div_assoc, ← mul_div_assoc, ← t1, ← t2]
    rw [map_add (f := _), hl] at n2 ⊢
    rw [h1] at n1 ⊢
    have n4 := left_ne_zero_of_mul n1
    simp only [hermForm]
    generalize χ l * Complex.exp _ = c at n4 ⊢
    generalize valAt' _ _ (w.s (ix φ j i)).val = a at n3 ⊢
    beta_reduce
    field_simp

end GlobalTheory.FrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDiscStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_arcLetterRingOverDVR_disc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  first | exact @GlobalTheory.LetterEval.exists_eval | exact GlobalTheory.LetterEval.exists_eval | (intros; apply GlobalTheory.LetterEval.exists_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinSiteNormEqZpowSiteAlg
section
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_finSite_norm_eq_zpow_siteAlg :
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (w : HeightOneSpectrum (𝓞 K₁)),
      (∃ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes ∧ OverLa w Tv.V io 1) ∧
      ∀ (Tv : CDVR) (io : K₁ →+* Tv.Fr), Tv.FinRes → OverLa w Tv.V io 1 →
        ∃ (Z : FinSite K₁ w) (ιT : Tv.Fr →+* Z.K), ιT.comp io = Z.ι ∧
          (∀ x : Tv.Fr, x ≠ 0 → ‖ιT x‖ = Z.r ^ vV Tv.V x) ∧ SiteAlg Z Tv ιT := by
  intro K₁ _ _ w
  obtain ⟨h1, h2⟩ := exists_finSite_siteAlg K₁ w
  refine ⟨h1, fun Tv io hfin ho => ?_⟩
  obtain ⟨Z, ιT, hc, hn, hs⟩ := h2 Tv io 1 hfin ho
  refine ⟨Z, ιT, hc, fun x hx => ?_, hs⟩
  have hf : ∀ v, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1 := fun v => (hn _).2 ⟨v, rfl⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Tv.V
  obtain ⟨y, hy⟩ := w.valuation_exists_uniformizer K₁
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hv : vLa w y = 1 := by
    rw [vLa, hy, WithZero.log_exp, neg_neg]
  have e1 : ‖Z.ι y‖ = Z.r := by
    have := Z.norm_ι y hy0
    rw [this]
    change Z.r ^ vLa w y = Z.r
    rw [hv, zpow_one]
  have e2 : ‖ιT (algebraMap Tv.V Tv.Fr π)‖ = Z.r := by
    rw [← e1, ← hc, RingHom.comp_apply,
      norm_map_eq_zpow_vV ιT hf hπ ((map_ne_zero io).2 hy0), ho.2 y, hv]
    simp
  rw [norm_map_eq_zpow_vV ιT hf hπ hx, e2]

end GlobalTheory.ArcQ
end
end

