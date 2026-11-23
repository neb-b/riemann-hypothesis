module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoordsBasisEigenLatticeSpan
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open scoped MonObj

namespace GlobalTheory.PtDeg.FrameExact
open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

section
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

lemma comb_add' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c c' : Fin n → R) :
    comb v (c + c') = comb v c * comb v c' :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_add hv
    ((isLieComb_iff_comb _ _ _).2 rfl) ((isLieComb_iff_comb _ _ _).2 rfl))).symm

lemma comb_zero' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) :
    comb v 0 = 1 :=
  ((isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_zero hv)).symm

lemma comb_sum' {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) {κ : Type}
    (s : Finset κ) (f : κ → Fin n → R) : comb v (∑ j ∈ s, f j) = ∏ j ∈ s, comb v (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using comb_zero' hv
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, comb_add' hv, ih]

lemma comb_comb' {n m : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i))
    (w : Fin m → (epsR R ⟶ G)) (B : Fin m → Fin n → R) (hw : ∀ j, w j = comb v (B j)) (g : Fin m → R) :
    comb w g = comb v (∑ j, g j • B j) := by
  rw [comb_sum' hv]
  unfold comb
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hw j]
  exact epsScale_comb v (B j) (g j)

lemma comb_comp_hom' {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f]
    {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) :
    comb v c ≫ f = comb (fun i => v i ≫ f) c :=
  (isLieComb_iff_comb _ _ _).1 (GlobalTheory.LieCombHom.isLieComb_comp f ((isLieComb_iff_comb _ _ _).2 rfl))

end
end GlobalTheory.PtDeg.FrameExact


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in
theorem GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp (𝓞 K))) (F : GlobalTheory.CM.GenFib P) (f : P.A ⟶ P.A) (M : F.P₀.A ⟶ F.P₀.A) [IsMonHom M] (L : Module.End K (Fin F.P₀.g → K)), F.IsDiffOf F f L → Over.Hom.left M ≫ F.φ = F.φ ≫ Over.Hom.left f → ∀ c : Fin F.P₀.g → K, GlobalTheory.Reg.VecEig.comb F.v c ≫ M = GlobalTheory.Reg.VecEig.comb F.v (L c) := by
  intro K _ _ P F f M _ L hL hM
  have hv := F.basis
  let Sg : Submodule K (Fin F.P₀.g → K) :=
    { carrier := {c | comb F.v c ≫ M = comb F.v (L c)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at *
        rw [comb_add' hv.1, map_add (f := _), comb_add' hv.1, ← ha, ← hb, MonObj.mul_comp]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, comb_zero' hv.1, MonObj.one_comp]
      smul_mem' := by
        intro s a ha
        simp only [Set.mem_ofPred_eq] at *
        rw [map_smul, ← epsScale_comb, ← epsScale_comb, ← ha, Category.assoc] }
  have hspan : Submodule.span K {c | ∃ u, F.IsCoord u c} = ⊤ := by
    have := (GlobalTheory.CM.LieLattice.lieLat_fg_and_span_eq_top K P F).2
    rw [GlobalTheory.CM.GenFib.lieLat, Submodule.span_span_of_tower] at this
    exact this
  have hpb : IsPullback F.φ F.P₀.A.hom P.A.hom (spMap (algebraMap (𝓞 K) K)) := F.fib.2.1.1
  have hsub : {c | ∃ u, F.IsCoord u c} ⊆ (Sg : Set _) := by
    rintro c ⟨u, hut, w, hwv, hwc⟩
    obtain ⟨hut', w', hw'v, hw'c⟩ := hL u c ⟨hut, w, hwv, hwc⟩
    obtain ⟨z, -, hz⟩ := GlobalTheory.existsUnique_isVecOver hpb (u ≫ f)
    have hwM : GlobalTheory.IsVecOver (algebraMap (𝓞 K) K) F.φ (u ≫ f) (w ≫ M) := by
      unfold GlobalTheory.IsVecOver at hwv ⊢
      simp only [Over.comp_left, Category.assoc]
      rw [hM, ← Category.assoc, hwv, Category.assoc]
    have e := (hz _ hwM).trans (hz _ hw'v).symm
    show comb F.v c ≫ M = comb F.v (L c)
    rw [(isLieComb_iff_comb _ _ _).1 hwc] at e
    rw [← (isLieComb_iff_comb _ _ _).1 hw'c, e]
  intro c
  have h := Submodule.span_le.2 hsub
  rw [hspan] at h
  exact h (Submodule.mem_top : c ∈ ⊤)


open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent GlobalTheory.PtDeg.FrameExact in
theorem GlobalTheory.PtDeg.exists_frameCoord_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ' : E →+* ℂ) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ' a)) → ∃ v : Fin (Dw.mult ρ') → Fin F.P₀.g → K, GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ' v ∧ LinearIndependent K v ∧ Submodule.span K (Set.range v) = Submodule.span K (F.eigLat B.t.act t : Set (Fin F.P₀.g → K)) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ' t ht
  have h1 : IsGrpPullback t₀.G Xo.univ.t.G y.x m1.φ := m1.cart
  have h2 : IsGrpPullback t₀.G B.t.G (spMap (algebraMap (𝓞 K) K)) m2.φ := m2.cart
  have h3 : IsGrpPullback F.P₀.A B.pol.A (spMap (algebraMap (𝓞 K) K)) F.φ := F.fib.2.1
  obtain ⟨⟨ψ, hψ, -⟩, hψm⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h2 h3 (𝟙 _)
  obtain ⟨⟨ψ', hψ', -⟩, hψm'⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h2 (𝟙 _)
  haveI : IsMonHom ψ := hψm ψ hψ inferInstance
  haveI : IsMonHom ψ' := hψm' ψ' hψ' inferInstance
  simp only [Over.id_left, Category.comp_id] at hψ hψ'
  have hψψ' : ψ ≫ ψ' = 𝟙 _ := by
    apply GlobalTheory.Reg.VecEig.pt_ext m2
    simp only [Over.comp_left, Category.assoc, Over.id_left, Category.id_comp]
    rw [hψ', hψ]
  have hψ'ψ : ψ' ≫ ψ = 𝟙 _ := by
    obtain ⟨⟨k, hk, hk1⟩, -⟩ := GlobalTheory.LamF.existsUnique_hom_of_isGrpPullback _ _ _ _ _ _ _ _ _ h3 h3 (𝟙 _)
    have a1 := hk1 (ψ' ≫ ψ) (by simp only [Over.comp_left, Category.assoc, Over.id_left, Category.comp_id]; rw [hψ, hψ'])
    have a2 := hk1 (𝟙 _) (by simp)
    rw [a1, a2]
  obtain ⟨r, hrD, hr⟩ := GlobalTheory.CM.GenFib.exists_lieRep_eigLat K B.pol F (𝓞 E) B.t.act
  have hv := F.basis

  have key : ∀ (u : epsR K ⟶ t₀.G) (d : Fin F.P₀.g → K), u ≫ ψ = comb F.v d → ∀ a : 𝓞 E,
      (u ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ u ↔ r a d = t a • d) := by
    intro u d hud a
    haveI := t₀.act.hom a
    have hM : Over.Hom.left (ψ' ≫ t₀.act.act a ≫ ψ) ≫ F.φ = F.φ ≫ Over.Hom.left (B.t.act.act a) := by
      simp only [Over.comp_left, Category.assoc, hψ]
      have := m2.act a
      simp only [SABMap.φ] at hψ' ⊢
      rw [this, ← Category.assoc, hψ']
    have hE := GlobalTheory.PtDeg.FrameExact.comb_comp_eq_of_isDiffOf K B.pol F (B.t.act.act a) (ψ' ≫ t₀.act.act a ≫ ψ) (r a) (hrD a) hM d
    rw [← hud] at hE
    have hE' : u ≫ t₀.act.act a ≫ ψ = comb F.v (r a d) := by
      rw [← hE]; simp only [Category.assoc, reassoc_of% hψψ']
    have hs : comb F.v (((t a : 𝓞 K) : K) • d) = epsScale ((t a : 𝓞 K) : K) ≫ u ≫ ψ := by
      rw [hud, epsScale_comb]
    have hsm : ((t a : 𝓞 K) : K) • d = t a • d := algebraMap_smul K (t a) d
    constructor
    · intro h
      apply comb_injective hv
      rw [← hE', ← hsm, hs, ← Category.assoc, h, Category.assoc]
    · intro h
      have h' : (u ≫ t₀.act.act a) ≫ ψ = (epsScale ((t a : 𝓞 K) : K) ≫ u) ≫ ψ := by
        rw [Category.assoc, hE', h, ← hsm, hs, Category.assoc]
      have := congrArg (· ≫ ψ') h'
      simpa only [Category.assoc, hψψ', reassoc_of% hψψ', Category.comp_id] using this

  have hlift : ∀ i, ∃ u : epsR K ⟶ t₀.G, Over.Hom.left u ≫ m1.φ = y.u ρ' i :=
    fun i => GlobalTheory.KSExist.FrameLift.exists_lift h1 (T := epsR K) (y.u ρ' i) (y.tan ρ' i).1
  choose U hU using hlift
  have hUt : ∀ i, IsTangent (U i) := fun i =>
    (GlobalTheory.KSExist.FrameLift.tan_iff h1 (U i)).1 (by rw [hU]; exact y.tan ρ' i)
  have hUe : ∀ i a, U i ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ U i := fun i a =>
    (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (U i) _).1 (by
      have := y.eig ρ' i a
      rw [hU, ht]; simpa only [Category.assoc] using this)
  have hWt : ∀ i, IsTangent (U i ≫ ψ) := fun i => GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ (hUt i)
  have hco : ∀ i, ∃ d, U i ≫ ψ = comb F.v d := fun i => by
    obtain ⟨d, hd, -⟩ := hv.2 _ (hWt i)
    exact ⟨d, (isLieComb_iff_comb _ _ _).1 hd⟩
  choose V hV using hco
  have hUy : (fun i => Over.Hom.left (U i) ≫ m1.φ) = y.u ρ' := funext hU
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i
    refine ⟨Over.Hom.left (U i), U i ≫ ψ, hU i, ?_, ?_⟩
    · simp only [Over.comp_left, Category.assoc, hψ]
    · rw [isLieComb_iff_comb]; exact hV i
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have e1 : comb U g ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV, hg]
    have e0 : comb U 0 ≫ ψ = comb F.v 0 := by
      rw [comb_comp_hom', comb_comb' hv.1 _ V hV]; simp
    have hW : comb U g = comb U 0 := by
      have := congrArg (· ≫ ψ') (e1.trans e0.symm)
      simpa only [Category.assoc, hψψ', Category.comp_id] using this
    have c1 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U g (comb U g) ((isLieComb_iff_comb _ _ _).2 rfl)
    have c0 := GlobalTheory.LieBasisRing.isCombAt_of_isLieComb h1 U 0 (comb U g) ((isLieComb_iff_comb _ _ _).2 hW)
    rw [hUy] at c1 c0
    have htan := GlobalTheory.ReframeClauses.isTanAt_of_isCombAt (y.tan ρ') c1
    have heig := GlobalTheory.ReframeClauses.isEigAt_of_isCombAt (y.tan ρ') (y.eig ρ') c1
    obtain ⟨a0, -, huniq⟩ := y.basis ρ' _ htan heig
    have := (huniq g c1).trans (huniq 0 c0).symm
    intro i
    simpa using congrFun this i
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ((hr t (V i)).2).2 fun a => (key (U i) (V i) (hV i) a).1 (hUe i a)
    · intro d hd
      have hd' := ((hr t d).2).1 hd
      have hwt : IsTangent (comb F.v d) := isTangent_comb hv.1 d
      have hu : (comb F.v d ≫ ψ') ≫ ψ = comb F.v d := by
        simp only [Category.assoc, hψ'ψ, Category.comp_id]
      have hut : IsTangent (comb F.v d ≫ ψ') := GlobalTheory.CM.DiffCoord.isTangent_comp_hom ψ' hwt
      have hue : ∀ a, (comb F.v d ≫ ψ') ≫ t₀.act.act a = epsScale ((t a : 𝓞 K) : K) ≫ (comb F.v d ≫ ψ') :=
        fun a => (key _ d hu a).2 (hd' a)
      have htan : IsTanAt y.x (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) :=
        (GlobalTheory.KSExist.FrameLift.tan_iff h1 _).2 hut
      have heig : IsEigAt c ρ' (Over.Hom.left (comb F.v d ≫ ψ') ≫ m1.φ) := fun a => by
        have := (GlobalTheory.KSExist.FrameLift.eig_iff h1 (m1.act a) (comb F.v d ≫ ψ') _).2 (hue a)
        rw [← ht]; simpa only [Category.assoc] using this
      obtain ⟨g, hg, -⟩ := y.basis ρ' _ htan heig
      rw [← hUy] at hg
      have hl := GlobalTheory.KSExist.FrameLift.isLieComb_of_isCombAt h1 U g _ hg
      rw [isLieComb_iff_comb] at hl
      have hdd : comb F.v d = comb F.v (∑ j, g j • V j) := by
        rw [← hu, hl, comb_comp_hom', comb_comb' hv.1 _ V hV]
      rw [comb_injective hv hdd]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralLabels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_integral_labels : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ (k : ℕ), 0 < k → ∀ (ζ : ℂˣ) (q : (Fin (2 * g) → ZMod k) → N.QT k), QLevel N g k ζ q → ∃ M Nn : (Fin (2 * g) → ZMod k) → Fin g → ℤ, (∀ a, d.Rep σ k (M a) (Nn a) (q a)) ∧ (∀ a a', ∃ M' N', M (a + a') = M a + M a' + (k : ℤ) • M' ∧ Nn (a + a') = Nn a + Nn a' + (k : ℤ) • N') ∧ (∀ a a' M' N', M a' = M a + (k : ℤ) • M' → Nn a' = Nn a + (k : ℤ) • N' → a = a') ∧ (∀ M₁ N₁, ∃ a M' N', M₁ = M a + (k : ℤ) • M' ∧ N₁ = Nn a + (k : ℤ) • N') ∧ ∀ i j, Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv (M (Pi.single i 1)) ⬝ᵥ cv (Nn (Pi.single j 1)) - cv (Nn (Pi.single i 1)) ⬝ᵥ cv (M (Pi.single j 1))) / k) = ((ζ ^ stdSymp g i j : ℂˣ) : ℂ) := by
  intro N g' r g bX d σ k hk ζ q hq
  obtain ⟨-, hadd, hinj, hsurj, hwp⟩ := hq
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.MBLow.Cl.torsion_eq_periods_mod N g' r g bX d σ k hk
  have h5 := _root_.GlobalTheory.MBLow.Cl.wp_classical N g' r g bX d σ k hk
  choose M0 N0 hMN using h1
  refine ⟨fun a => M0 (q a), fun a => N0 (q a), fun a => hMN _, fun a a' => ?_, fun a a' M' N' hM hN => ?_,
    fun M₁ N₁ => ?_, fun i j => ?_⟩
  · exact (h4 _ _ _ _ _ _ (h3 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))) (hMN (q (a + a')))).1 (hadd a a')
  · exact hinj a a' ((h4 _ _ _ _ _ _ (hMN (q a)) (hMN (q a'))).2 ⟨M', N', hM, hN⟩)
  · obtain ⟨p, hp, -⟩ := h2 M₁ N₁
    obtain ⟨a, ha⟩ := hsurj p
    exact ⟨a, (h4 _ _ _ _ _ _ (hMN (q a)) hp).1 ha⟩
  · rw [← hwp i j]
    exact (h5 _ _ _ _ _ _ (hMN _) (hMN _)).symm

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCancelPulledBundlesGerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.IsoComp

theorem pullIsoAlong {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (G : Y ⟶ XG) (hG : θ ≫ φ = G)
    {LP : LB XA} {LL : LB XG} (ψ : LB.Iso LP (LL.pull φ)) (hψ : PGen ψ) :
    ∃ w : LB.Iso (LP.pull θ) (LL.pull G), PGen w ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), G (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) := by
  subst hG
  have hle : ∀ (J : PUnit → LL.ι) (K : PUnit → LP.ι),
      (LL.pull (θ ≫ φ)).U J ⊓ (LP.pull θ).U K ≤ θ ⁻¹ᵁ ((LL.pull φ).U J ⊓ LP.U (K PUnit.unit)) :=
    fun J K x hx => ⟨(mem_pull (F := φ)).2 ((mem_pull (F := θ ≫ φ)).1 hx.1), (mem_pull (F := θ)).1 hx.2⟩
  obtain ⟨w, hw⟩ : ∃ w : LB.Iso (LP.pull θ) (LL.pull (θ ≫ φ)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (K : PUnit → LP.ι), (θ ≫ φ) (r z) ∈ LL.U i →
        r z ∈ (LP.pull θ).U K → gw w r z i K = gw ψ (r ≫ θ) z i (K PUnit.unit) :=
    ⟨⟨fun p => res (hle p.1 p.2) (pullU θ _ (ψ.s (p.1, p.2 PUnit.unit)))⟩, fun Z r z i K hi hK =>
      (gm_res r z (hle (fun _ => i) K) ⟨mem_pull.2 hi, hK⟩ _).trans
        (gm_pull r θ z _ (hle (fun _ => i) K ⟨mem_pull.2 hi, hK⟩) _)⟩
  refine ⟨w, fun Z r z j j' k k' hj hj' hk hk' => ?_, hw⟩
  rw [hw Z r z j k hj hk, hw Z r z j' k' hj' hk', gm_pull_g LP θ r z k k' hk hk',
    hψ Z (r ≫ θ) z j j' (k PUnit.unit) (k' PUnit.unit) hj hj' ((mem_pull (F := θ)).1 hk) ((mem_pull (F := θ)).1 hk'), Category.assoc]

theorem isoAsPullId {X : Scheme.{0}} {LL LM : LB X} (e : LB.Iso LM LL) (he : e.IsGen) :
    ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), PGen eP ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) := by
  have hle : ∀ (J : PUnit → LL.ι) (j : LM.ι), (LL.pull (𝟙 X)).U J ⊓ LM.U j ≤ LL.U (J PUnit.unit) ⊓ LM.U j :=
    fun J j x hx => ⟨mem_pull.1 hx.1, hx.2⟩
  obtain ⟨eP, hP⟩ : ∃ eP : LB.Iso LM (LL.pull (𝟙 X)), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (y : Y) (i : LL.ι) (j : LM.ι),
      f y ∈ LL.U i → f y ∈ LM.U j → gw eP f y i j = gm f y (LL.U i ⊓ LM.U j) (e.s (i, j)) :=
    ⟨⟨fun p => res (hle p.1 p.2) (e.s (p.1 PUnit.unit, p.2))⟩, fun Y f y i j hi hj =>
      gm_res f y (hle (fun _ => i) j) ⟨mem_pull.2 hi, hj⟩ _⟩
  refine ⟨eP, fun Y f y j j' k k' hj hj' hk hk' => ?_, hP⟩
  have hm : f y ∈ LL.U j ⊓ LM.U k ⊓ (LL.U j' ⊓ LM.U k') := ⟨⟨hj, hk⟩, hj', hk'⟩
  have hm' : f y ∈ (LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k') := hm
  have h1 := congrArg (gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k'))) (he (j, k) (j', k'))
  have hd : gm f y ((LB.div LL LM).U (j, k) ⊓ (LB.div LL LM).U (j', k')) ((LB.div LL LM).g (j, k) (j', k')) =
      gm f y (LL.U j ⊓ LL.U j') (LL.g j j') * (gm f y (LM.U k ⊓ LM.U k') (LM.g k k'))⁻¹ :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f y _ hm' _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res f y _ hm' _))))
  rw [hP Y f y j k hj hk, hP Y f y j' k' hj' hk', Category.comp_id]
  exact (gm_res f y inf_le_left hm' _).symm.trans (h1.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) hd (gm_res f y inf_le_right hm' _))))

theorem isoCancelGerm : ∀ {Y XA XG : Scheme.{0}} (θ : Y ⟶ XA) (φ : XA ⟶ XG) (fst : Y ⟶ XG), θ ≫ φ = fst →
    ∀ (LP : LB XA) (LL LM : LB XG), LP.IsLB → LL.IsLB → LM.IsLB →
    ∀ (ψ : LB.Iso LP (LL.pull φ)) (e : LB.Iso LM LL), ψ.IsGen → e.IsGen →
    ∃ w₀ : LB.Iso (LP.pull θ) (LM.pull fst), w₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : LL.ι) (j : LM.ι) (k : LP.ι),
        fst (r z) ∈ LL.U i → fst (r z) ∈ LM.U j → θ (r z) ∈ LP.U k →
        gw w₀ r z j (fun _ => k) = (gm (r ≫ fst) z (LL.U i ⊓ LM.U j) (e.s (i, j)))⁻¹ * gw ψ (r ≫ θ) z i k := by
  intro Y XA XG θ φ fst hfst LP LL LM hP hL hM ψ e hψ he
  obtain ⟨w'', hw'', hv''⟩ := pullIsoAlong θ φ (fst ≫ 𝟙 XG) (by rw [Category.comp_id, hfst]) ψ
    ((isGen_iff ψ).1 hψ)
  obtain ⟨eP, heP, hvP⟩ := isoAsPullId e he
  obtain ⟨w₀, T⟩ := exists_cancel hL eP w'' heP hw'' hM (pull_isLB hP θ)
  refine ⟨w₀, (isGen_iff w₀).2 (T.pgen_cancel hL heP hw''), fun Z r z i j k hi hj hk => ?_⟩
  have t := T Z r z i j (fun _ => k) hi hj (mem_pull.2 hk)
  rw [hv'' Z r z i (fun _ => k) hi (mem_pull.2 hk), hvP Z (r ≫ fst) z i j hi hj] at t
  rw [t, inv_mul_cancel_left]

end GlobalTheory.IsoComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace TopForm

namespace FrameBasis

theorem bijective_of_isFreeGen {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A) {m : ℕ}
    (hA : α.IsStandardSmoothOfRelativeDimension m) (x : Fin m → A)
    (hx : IsFreeGen A (dForm α x)) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension m k A := hA
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    haveI := Module.subsingleton A (Omega α)
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth m (R := k) (S := A)
    haveI : Module.Free A (Omega α) := inferInstanceAs (Module.Free A Ω[A⁄k])
    haveI : Module.Finite A (Omega α) := inferInstanceAs (Module.Finite A Ω[A⁄k])
    have hr : Module.finrank A (Omega α) = m := Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) m)
    let b := Module.finBasisOfFinrankEq A (Omega α) hr
    let v : Fin m → Omega α := fun i => dFun α (x i)
    obtain ⟨a, ha⟩ := hx.2 (exteriorPower.ιMulti A m b)
    have e := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) ha
    simp only [map_smul, dForm_eq, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      Module.Basis.det_self, smul_eq_mul] at e
    have hu : IsUnit (b.det v) := IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact e)
    obtain ⟨hli, hsp⟩ := (b.is_basis_iff_det).2 hu
    let b' := Module.Basis.mk hli hsp.ge
    have : (Fintype.linearCombination A fun i => dFun α (x i)) = b'.equivFun.symm.toLinearMap := by
      ext c
      simp [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, b', v]
    rw [this]
    exact b'.equivFun.symm.bijective

end FrameBasis

end TopForm

end GlobalTheory

namespace GlobalTheory.TopForm.FrameBasis

theorem bijective_of_isLocalization_span {k A : Type*} [CommRing k] [CommRing A] (α : k →+* A)
    {m : ℕ} (x : Fin m → A) (s : Set A) (hs : Ideal.span s = ⊤) (B : s → Type*)
    [∀ t, CommRing (B t)] [∀ t, Algebra A (B t)] [∀ t : s, IsLocalization.Away t.1 (B t)]
    (H : ∀ t : s, Function.Bijective (Fintype.linearCombination (B t)
      fun i => dFun ((algebraMap A (B t)).comp α) (algebraMap A (B t) (x i)))) :
    Function.Bijective (Fintype.linearCombination A fun i => dFun α (x i)) := by
  letI := α.toAlgebra
  letI (t : s) : Algebra k (B t) := ((algebraMap A (B t)).comp α).toAlgebra
  haveI (t : s) : IsScalarTower k A (B t) := IsScalarTower.of_algebraMap_eq' rfl
  haveI (t : s) : Algebra.FormallyEtale A (B t) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t.1)
  let g : ∀ t : s, Ω[A⁄k] →ₗ[A] Ω[B t⁄k] := fun t => KaehlerDifferential.map k k A (B t)
  haveI H₁ (t : s) : IsLocalizedModule.Away t.1 (g t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (g t)).2
      (KaehlerDifferential.isBaseChange_of_formallyEtale k A (B t))
  let π : ∀ t : s, (Fin m → A) →ₗ[A] (Fin m → B t) := fun t => (Algebra.linearMap A (B t)).compLeft (Fin m)
  haveI H₂ (t : s) : IsLocalizedModule.Away t.1 (π t) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t.1) (B t) (π t)).2
      (IsBaseChange.finitePow (Fin m) (IsBaseChange.linearMap A (B t)))
  let e : ∀ t : s, (Fin m → B t) ≃ₗ[A] Ω[B t⁄k] := fun t =>
    (LinearEquiv.ofBijective _ (H t)).restrictScalars A
  haveI H₃ (t : s) : IsLocalizedModule.Away t.1 ((e t).toLinearMap ∘ₗ π t) :=
    IsLocalizedModule.of_linearEquiv _ _ _
  have hcomp (t : s) : g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i)) =
      (e t).toLinearMap ∘ₗ π t := by
    ext c
    simp [g, e, π, Fintype.linearCombination_apply, algebraMap_smul]
  haveI H₄ (t : s) : IsLocalizedModule.Away t.1
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) := by
    rw [hcomp t]; exact H₃ t
  refine bijective_of_isLocalized_span s hs (fun t => Ω[B t⁄k])
    (fun t => g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (fun t => Ω[B t⁄k]) g
    (Fintype.linearCombination A fun i => dFun α (x i)) fun t => ?_
  have : IsLocalizedModule.map (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t)
      (Fintype.linearCombination A fun i => dFun α (x i)) = LinearMap.id := by
    refine IsLocalizedModule.linearMap_ext (.powers t.1)
      (g t ∘ₗ (Fintype.linearCombination A fun i => dFun α (x i))) (g t) ?_
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [this]
  exact Function.bijective_id

end GlobalTheory.TopForm.FrameBasis

namespace GlobalTheory.TopForm.FrameBasis

theorem exists_basis_of_isFrame : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (m : ℕ),
    SmoothOfRelativeDimension m p → ∀ (U : X.Opens) (x : Fin m → Γ(X, U)),
    GlobalTheory.TopForm.IsFrame (GlobalTheory.TopForm.dOn p x) →
    ∃ b : Module.Basis (Fin m) Γ(X, U) (GlobalTheory.TopForm.Omega (algX p U)),
      ∀ i, b i = GlobalTheory.TopForm.dFun (algX p U) (x i) := by
  intro k _ X p m hp U x hx
  have hU := hx.affine
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) p hp
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  haveI (t : (s : Set Γ(X, U))) := hU.isLocalization_basicOpen t.1
  have hbij : Function.Bijective
      (Fintype.linearCombination Γ(X, U) fun i => dFun (algX p U) (x i)) := by
    refine bijective_of_isLocalization_span (algX p U) x (s : Set Γ(X, U)) hs
      (fun t => Γ(X, X.basicOpen t.1)) fun t => ?_
    have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
      (h t t.2 Γ(X, X.basicOpen t.1))
    have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen t.1)).comp (algX p U) =
        algX p (X.basicOpen t.1) := resG_comp_algX p (X.basicOpen_le t.1)
    have h₂ : (algX p (X.basicOpen t.1)).IsStandardSmoothOfRelativeDimension m := by
      rw [← resG_comp_algX p (X.basicOpen_le t.1)]
      exact h₁
    have hfr := (hx.res (hU.basicOpen t.1) (X.basicOpen_le t.1)).gen
    rw [resForm_dOn] at hfr
    have := bijective_of_isFreeGen _ h₂ _ hfr
    rw [e]
    exact this
  let eq := LinearEquiv.ofBijective _ hbij
  refine ⟨Module.Basis.ofEquivFun eq.symm, fun i => ?_⟩
  simp [eq, Module.Basis.coe_ofEquivFun, Fintype.linearCombination_apply, Pi.single_apply]

end GlobalTheory.TopForm.FrameBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegularStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specializes_dominatesStalk_of_regular : ∀ (X : Scheme.{0}) [IsIntegral X] (V : ValuationSubring X.functionField) (y : X), (∀ g, RegAt y g → g ∈ V) → ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  first | exact @GlobalTheory.exists_specializes_dominatesStalk_of_regAt | exact GlobalTheory.exists_specializes_dominatesStalk_of_regAt | (intros; apply GlobalTheory.exists_specializes_dominatesStalk_of_regAt <;> assumption)
end

