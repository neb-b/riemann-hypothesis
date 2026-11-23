module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0133
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteTopologyRatN
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ConstNotCusp

variable (E : Type) [Field E] [NumberField E] (a r : ℕ)

theorem discreteTopology_ratN : DiscreteTopology (ratN E a r) := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hW : IsOpen (Set.pi Set.univ fun _ : BlockIx a r => V) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hVo
  convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratN E a r)) using 1
  ext ⟨_, x, rfl⟩
  constructor
  · intro h p _
    have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
    exact h1.symm ▸ hV0
  · intro h
    have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
    subst hx
    exact Subtype.ext (map_zero _)

theorem exists_compact_ratN : ∃ K : Set (BlockIx a r → Ad E), IsCompact K ∧
    ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  choose y hy using fun p => h (x p)
  refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
  change algebraMap E (Ad E) (-y p) + x p ∈ K
  rw [map_neg, neg_add_eq_sub]
  exact hy p

theorem not_isCuspidal_oneFn : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    2 ≤ a → ¬ IsCuspidal (oneFn E a).1 := by
  intro E _ _ _ a ha h
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  letI : MeasurableSpace (BlockIx a 1 → Ad E) := borel _
  haveI : BorelSpace (BlockIx a 1 → Ad E) := ⟨rfl⟩
  haveI := discreteTopology_ratN E a 1
  obtain ⟨K, hK, hcov⟩ := exists_compact_ratN E a 1
  obtain ⟨⟨μ, F, hμ, hF, h1⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratN E a 1) K hK hcov
  have h2 : ∫ _ in F, (1 : ℂ) ∂μ = 0 := h 1 one_pos (by omega) μ F hμ hF 1
  simp [Measure.real, h1] at h2

end GlobalTheory.ConstNotCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroups
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem cbe_iff {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {r h' κ s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) (hκ : κ ∈ J) :
    s ∈ Loc.Cbe J (r * h' * κ) ↔ r⁻¹ * s * r ∈ Loc.Cbe J h' := by
  constructor
  · rintro ⟨hs1, hs2⟩
    refine ⟨(Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem ((Loc.R1 k n c).inv_mem hr) hs1) hr, ?_⟩
    have h2 : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J := hs2
    show h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J
    have e : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ = κ * ((r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹) * κ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hκ h2) (inv_mem hκ)
  · rintro ⟨hs1, hs2⟩
    have hs1' : s ∈ Loc.R1 k n c := by
      have := (Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem hr hs1) ((Loc.R1 k n c).inv_mem hr)
      rwa [show r * (r⁻¹ * s * r) * r⁻¹ = s by group] at this
    refine ⟨hs1', ?_⟩
    have h2 : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J := hs2
    show (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J
    have e : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ = κ⁻¹ * (h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹) * κ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hκ) h2) hκ

theorem red_conj {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (δ : GLint E n P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ y ∈ stdAt E n P, redV P (g y) = A.1.mulVec (redV P y)) :
    ∀ y ∈ stdAt E n P, redV P ((δ.1 * g * δ.1⁻¹) y) =
      (GlobalTheory.TopStep.redGL n P δ * A * (GlobalTheory.TopStep.redGL n P δ)⁻¹).1.mulVec (redV P y) := by
  intro y hy
  have h1 : δ.1⁻¹ y ∈ stdAt E n P := ((δ⁻¹).2 y).2 hy
  have h2 : g (δ.1⁻¹ y) ∈ stdAt E n P := (hg _).2 h1
  show redV P (δ.1 (g (δ.1⁻¹ y))) = _
  rw [GlobalTheory.TopStep.redV_redGL δ h2, hA _ h1]
  have h3 := GlobalTheory.TopStep.redV_redGL δ⁻¹ hy
  have e : (δ⁻¹).1 y = δ.1⁻¹ y := rfl
  rw [e] at h3
  rw [h3, map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem inX_mem_lamYat_iff {X : Fields} {Pr : Primes X} {R : Ranks} (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : Sp X.E (R.N j)) :
    Loc.inX X.E (R.N j) (cOf R j) x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ stdAt X.E (R.N j) P := by
  unfold lamYat
  rw [if_pos hP]
  exact ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
    GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩

theorem lamRow_tup {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu mu' : Tup X.F X.E X.K S) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (f : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) :
    lamRow Ch mu true j P f = lamRow Ch mu' true j P f := by
  unfold lamRow
  simp only [if_pos hP, if_true]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem loc_match : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  intro X Pr R Ch sel S mu mu' cst cst' L L' G m2 _ _ _ hs hs' hok hok' j hj b b' w r κ hr hκ he
  have hP : w.1 ∈ Pr.vGs := w.2
  have hjm : j < R.m := by rw [hok.hm]; omega
  have hG := hok.grpG j b w
  have hG' := hok'.grpG j b' w
  have hC := hok.chrG j b w
  have hC' := hok'.chrG j b' w
  have hint := hok.int j b ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hint' := hok'.int j b' ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hst := hok.stabG j b ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hst' := hok'.stabG j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hpsi := fun a ha => hok.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  have hpsi' := fun a ha => hok'.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  rw [hs] at hG hC hint
  rw [hs'] at hG' hC' hint'
  unfold chiInv at hC hC'
  rw [hs] at hC
  rw [hs'] at hC'
  generalize L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = h at hG hC hint hst he
  generalize L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ = h' at hG' hC' hint' hst' he
  subst he

  have hκs := jat_le_stab_lamY true j w.1 hP κ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j w.1) := by
    have := mul_mem (mul_mem hst (inv_mem hκs)) (inv_mem hst')
    rwa [show r * h' * κ * κ⁻¹ * h'⁻¹ = r by group] at this
  obtain ⟨γ, hγ⟩ := GlobalTheory.QNormal.exists_res hr
  have hγint : γ ∈ GLint X.E (R.N j) w.1 := by
    intro y
    rw [← inX_mem_lamYat_iff (Pr := Pr) j hP, ← inX_mem_lamYat_iff (Pr := Pr) j hP, ← hγ y]
    exact hrs _
  set γg : GLint X.E (R.N j) w.1 := ⟨γ, hγint⟩ with hγg
  refine ⟨GlobalTheory.TopStep.redGL (R.N j) w.1 γg⁻¹, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    have e : γ = 1 := by
      refine LinearEquiv.ext fun y => GlobalTheory.QNormal.inX_injective (c := cOf R j) ?_
      rw [← hγ y]
      rfl
    have e2 : γg = 1 := Subtype.ext e
    rw [e2, inv_one, map_one]
  · intro hbar
    rw [hG, hG']
    constructor
    · rintro ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩
      refine ⟨γ⁻¹ * g * γ, ⟨r⁻¹ * r₁ * r, (cbe_iff _ hr hκ).1 hr₁, GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres⟩, ?_⟩
      intro y hy
      exact red_conj γg⁻¹ (hint ⟨r₁, hr₁, hres⟩) hred y hy
    · rintro ⟨g', ⟨r₁', hr₁', hres'⟩, hred'⟩
      have hγ' : ∀ y, r⁻¹ (Loc.inX X.E (R.N j) (cOf R j) y) = Loc.inX X.E (R.N j) (cOf R j) (γ⁻¹ y) := by
        intro y
        show r.symm _ = _
        rw [LinearEquiv.symm_apply_eq, hγ]
        show _ = Loc.inX X.E (R.N j) (cOf R j) (γ (γ.symm y))
        rw [LinearEquiv.apply_symm_apply]
      have hmem : r * r₁' * r⁻¹ ∈ Loc.Cbe (Jat (Pr := Pr) true j w.1) (r * h' * κ) := by
        refine (cbe_iff _ hr hκ).2 ?_
        rwa [show r⁻¹ * (r * r₁' * r⁻¹) * r = r₁' by group]
      refine ⟨γ * g' * γ⁻¹, ⟨r * r₁' * r⁻¹, hmem, fun y => GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ' hres' y⟩, ?_⟩
      intro y hy
      have e : ∀ (Q A : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Q * (Q⁻¹ * A * Q⁻¹⁻¹) * Q⁻¹ = A := by
        intro Q A
        group
      have := red_conj γg (hint' ⟨r₁', hr₁', hres'⟩) hred' y hy
      rw [map_inv, e] at this
      exact this
  · intro hbar hbar' hx
    obtain ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩ := (hG hbar.1).1 hbar.2
    have hgint := hint ⟨r₁, hr₁, hres⟩
    have hr₁' := (cbe_iff _ hr hκ).1 hr₁
    have hres' := GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres
    have hred' : ∀ y ∈ stdAt X.E (R.N j) w.1, redV w.1 ((γ⁻¹ * g * γ) y) = hbar'.1.1.mulVec (redV w.1 y) := by
      intro y hy
      rw [hx]
      exact red_conj γg⁻¹ hgint hred y hy
    have e1 := hC hbar g r₁ hr₁ hres hred
    have e2 := hC' hbar' (γ⁻¹ * g * γ) (r⁻¹ * r₁ * r) hr₁' hres' hred'
    refine Units.ext ?_
    rw [e1, e2, GlobalTheory.Proof.level_eq_parahoric_category.n1Arg_conj_eq hr hr₁.1]

    have hr₁s : r₁ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) := by
      have h1 : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁.2
      have h2 := jat_le_stab_lamY true j w.1 hP _ h1
      have h3 := mul_mem (mul_mem hst h2) (inv_mem hst)
      rw [show r * h' * κ * ((r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹) * (r * h' * κ)⁻¹ = r₁ by group] at h3
      unfold lamYat at h3
      rw [if_pos hP] at h3
      exact h3
    have hq := GlobalTheory.TopStep.qOf_ne_zero (P := w.1) (E := X.E)
    have hia := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r₁ hr₁s
    have ea : ((qOf w.1 : ℕ) : X.E) * Loc.n1Arg r₁ / ((qOf w.1 : ℕ) : X.E) = Loc.n1Arg r₁ := by
      field_simp
    have p1 := hpsi _ hia
    have p2 := hpsi' _ hia
    rw [ea] at p1 p2
    rw [p1, p2]
    congr 1

    rw [lamRow_tup Ch mu mu' j hP]
    have ht : h'⁻¹ * (r⁻¹ * r₁ * r) * h'⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁'.2
    rw [inv_inv] at ht
    have e : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ) = κ⁻¹ * (h'⁻¹ * (r⁻¹ * r₁ * r) * h') * κ := by group
    rw [e]
    generalize h'⁻¹ * (r⁻¹ * r₁ * r) * h' = t at ht ⊢
    have LM := GlobalTheory.SymLevelMul.lamRow_mul Ch mu' j w.1 hjm hP
    have hκi : κ⁻¹ ∈ Jat (Pr := Pr) (R := R) true j w.1 := inv_mem hκ
    rw [LM _ (mul_mem hκi ht) _ hκ, LM _ hκi _ ht]
    have e3 : lamRow Ch mu' true j w.1 t.toLinearMap =
        lamRow Ch mu' true j w.1 t.toLinearMap * lamRow Ch mu' true j w.1 (κ⁻¹ : AutY X R j).toLinearMap *
          lamRow Ch mu' true j w.1 κ.toLinearMap := by
      conv_lhs => rw [show t = t * κ⁻¹ * κ by group]
      rw [LM _ (mul_mem ht hκi) _ hκ, LM _ ht _ hκi]
    linear_combination -e3

end GlobalTheory.Mem.Col2.IdxEx.LocMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSections
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem mem_nonZeroDivisors_of_dense_compl_support {W T : Scheme.{0}} (I : W.IdealSheafData) (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (hd : ∀ t : T, d t ∉ I.support)
    (A : W.affineOpens) (s : Γ(W, A.1)) (hs : I.ideal A = Ideal.span {s}) : s ∈ nonZeroDivisors Γ(W, A.1) := by
  have hu : IsUnit (d.app A.1 s) := by
    refine T.toRingedSpace.isUnit_of_isUnit_germ _ _ fun t ht => ?_
    refine (T.mem_basicOpen _ t ht).1 ?_
    rw [← Scheme.preimage_basicOpen]
    have h := hd t
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) ht, hs, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at h
    exact not_not.1 h
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply d.app_injective A.1
  have h := congrArg (d.app A.1) hx
  rw [map_mul, map_zero] at h
  rw [map_zero]
  exact hu.mul_left_eq_zero.1 h

theorem effCartier_of_proportional (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X)
    (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W)
    (hI : GeneratesAlong I σ g) (hp : Proportional σ g ψ) (h₁ : IsSchemeTheoreticallyDominant d)
    (h₂ : QuasiCompact d) (hd : ∀ t : T, d t ∉ I.support) : FinalTheorems.EffCartier I := by
  intro w
  obtain ⟨k, hk⟩ : ∃ k, w ∈ g ⁻¹ᵁ L.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hI.1.ge (show w ∈ (⊤ : W.Opens) from trivial))
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart R m (ψ w)
  obtain ⟨A, hA, hw, hle⟩ := exists_isAffineOpen_mem_and_subset
    (show w ∈ g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i from ⟨hk, hi⟩)
  have hAk : A ≤ g ⁻¹ᵁ L.U k := fun x hx => (hle hx).1
  have hAi : A ≤ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i := fun x hx => (hle hx).2
  have hs : I.ideal ⟨A, hA⟩ = Ideal.span {(g.appLE (L.U k) A hAk).hom ((σ i).f k)} := by
    rw [hI.2 k ⟨A, hA⟩ hAk]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩))
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_span_singleton'.2 ⟨_, (hp A k hAk i hAi j).symm⟩
  exact ⟨⟨A, hA⟩, _, hw, mem_nonZeroDivisors_of_dense_compl_support I d hd ⟨A, hA⟩ _ hs, hs⟩

end GlobalTheory.ProjBlowup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfProportionalToGeneratingSections
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

theorem Proportional.basicOpen_le_chart {R : Type} [CommRing R] {X W : Scheme.{0}} {L : LB X} {m : ℕ}
    {σ : Fin (m + 1) → L.Sec} {g : W ⟶ X} {ψ : W ⟶ PSpace R m} (h : Proportional σ g ψ)
    (A : W.Opens) (k : L.ι) (hk : A ≤ g ⁻¹ᵁ L.U k) (i : Fin (m + 1)) :
    W.basicOpen ((g.appLE (L.U k) A hk).hom ((σ i).f k)) ≤ ψ ⁻¹ᵁ chart R m i := by
  intro z hz
  obtain ⟨i', hi'⟩ := (isCoordFamily_pullRatio ψ).exists_mem z
  have hA : z ∈ A := W.basicOpen_le _ hz
  have e := h (A ⊓ ψ ⁻¹ᵁ chart R m i') k (inf_le_left.trans hk) i' inf_le_right i
  have e' := congrArg W.basicOpen e
  rw [Scheme.basicOpen_mul, basicOpen_pullRatio, Scheme.basicOpen_appLE] at e'
  rw [Scheme.basicOpen_appLE] at hz
  have hz' : z ∈ (A ⊓ ψ ⁻¹ᵁ chart R m i') ⊓ g ⁻¹ᵁ X.basicOpen ((σ i).f k) := ⟨⟨hA, hi'⟩, hz.2⟩
  exact (e'.le hz').1.2

theorem eq_of_proportional :
    ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ ψ' : W ⟶ PSpace R m), GeneratesAlong ⊤ σ g → ψ ≫ PSpace.str R m = ψ' ≫ PSpace.str R m → Proportional σ g ψ → Proportional σ g ψ' → ψ = ψ' := by
  intro R _ X W L m σ g ψ ψ' hG hs h h'
  refine hom_ext hs fun y => ?_
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hG.1.ge (Set.mem_univ y))
  obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAk⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open hk (g ⁻¹ᵁ L.U k).isOpen
  have hAk' : A ≤ g ⁻¹ᵁ L.U k := hAk
  have hsp := hG.2 k ⟨A, hA⟩ hAk'
  have hsp' : Ideal.span (Set.range fun j => (g.appLE (L.U k) A hAk').hom ((σ j).f k)) = ⊤ := hsp.symm
  have hcov := (IsAffineOpen.self_le_iSup_basicOpen_iff hA).2 hsp'
  obtain ⟨⟨_, i, rfl⟩, hi⟩ := Opens.mem_iSup.1 (hcov hyA)
  have hB := W.basicOpen_le ((g.appLE (L.U k) A hAk').hom ((σ i).f k))
  refine ⟨_, hi, i, h.basicOpen_le_chart A k hAk' i, h'.basicOpen_le_chart A k hAk' i, fun j => ?_⟩
  have hu : IsUnit ((g.appLE (L.U k) _ (hB.trans hAk')).hom ((σ i).f k)) := by
    rw [← resG_appLE g hAk' hB]
    exact RingedSpace.isUnit_res_basicOpen _ _
  exact hu.mul_right_cancel ((h _ k _ i _ j).symm.trans (h' _ k _ i _ j))

end GlobalTheory.ProjBlowup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLatticesStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_indexIdeal_inf_sup_lattices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), GlobalTheory.BetaEx.Bdd (M' ⊔ M) → (∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') → ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ GlobalTheory.BetaEx.detSpan (M ⊓ M') = 𝔞 • GlobalTheory.BetaEx.detSpan M ∧ GlobalTheory.BetaEx.detSpan M' = 𝔞 • GlobalTheory.BetaEx.detSpan (M' ⊔ M) ∧ Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  first | exact @GlobalTheory.BetaEx.exists_index_ideal_inf_sup | exact GlobalTheory.BetaEx.exists_index_ideal_inf_sup | (intros; apply GlobalTheory.BetaEx.exists_index_ideal_inf_sup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveSeqNormOne
section
namespace GlobalTheory.InjectiveSeqNormOne

theorem exists_injective_seq_norm_one {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) :
    ∃ a : ℕ → E, Function.Injective a ∧ ∀ k : ℕ, a k * σ (a k) = 1 := by
  obtain ⟨-, hE, -, hσ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hσ, hσ, star_star])
  have hy : ∃ y, σ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hE.isComplex _
    rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [hcon] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  obtain ⟨y, hy⟩ := hy
  have h1 : ∀ k : ℕ, (k : E) + y ≠ 0 := by
    intro k hk
    apply hy
    have : y = -(k : E) := by linear_combination hk
    rw [this, map_neg, map_natCast]
  have h2 : ∀ k : ℕ, (k : E) + σ y ≠ 0 := by
    intro k hk
    apply h1 k
    have := congrArg σ hk
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine ⟨fun k => ((k : E) + y) / ((k : E) + σ y), ?_, ?_⟩
  · intro k m hkm
    have hkm' := (div_eq_div_iff (h2 k) (h2 m)).1 hkm
    have h3 : ((k : E) - m) * (σ y - y) = 0 := by linear_combination hkm'
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.1 h4
    · exact absurd (sub_eq_zero.1 h4) hy
  · intro k
    have a1 := h1 k
    have a2 := h2 k
    simp only [map_div₀, map_add (f := _), map_natCast, hinv]
    field_simp

end GlobalTheory.InjectiveSeqNormOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelGroup_mod_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j), cst.Ok → P.1 ∈ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) → prCat (Pr := Pr) cst.sharp j P.1 h ≤ GLint X.E (R.N j) P.1 → (∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P.1, y x ∈ lamYat (Pr := Pr) (R := R) j P.1) → lamRow Ch mu cst.sharp j P.1 (LinearMap.id + (qOf P.1 : X.E) • y) = 1) → ChiMul Ch sel mu cst j P h → ChiTriv Ch sel mu cst j P h → ∃ lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j), GrpG sel mu cst j P h lev ∧ ChrG Ch sel mu cst j P h lev := by
  first | exact @GlobalTheory.Mem.Col2.LevMod.exists_levG | exact GlobalTheory.Mem.Col2.LevMod.exists_levG | (intros; apply GlobalTheory.Mem.Col2.LevMod.exists_levG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem discreteTopology_subgroup_of_nhds_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Γ : Subgroup G) (h : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, (∃ γ : Γ, γ • (1 : G) = g) → g = 1) :
    DiscreteTopology Γ := by
  obtain ⟨U, hU, h⟩ := h
  refine discreteTopology_of_isOpen_singleton_one ?_
  obtain ⟨V, hVU, hV, h1⟩ := mem_nhds_iff.1 hU
  have e : ({1} : Set Γ) = Subtype.val ⁻¹' V := by
    ext γ
    constructor
    · rintro rfl
      exact h1
    · intro hγ
      exact Subtype.ext (h _ (hVU hγ) ⟨γ, by simp [Subgroup.smul_def]⟩)
  rw [e]
  exact hV.preimage continuous_subtype_val

theorem fundamentalDomain_exists_measure_eq_of_discrete {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] :
    (∃ 𝓕, IsFundamentalDomain Γ 𝓕 μ) ∧
      ∀ 𝓕 𝓕', IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  have := GlobalTheory.countable_of_discrete_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Γ
  exact ⟨⟨D, hD μ⟩, fun 𝓕 𝓕' h h' => ⟨h.measure_eq h', h.measure_ne_zero (NeZero.ne μ)⟩⟩

theorem fundamentalDomain_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ M J μ hμ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).2.1
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : DiscreteTopology Γ := discreteTopology_subgroup_of_nhds_one Γ (_root_.GlobalTheory.Mem.Vol.exists_nhds_one_rational_eq_one F E σ M J)
  exact fundamentalDomain_exists_measure_eq_of_discrete Γ μ

end GlobalTheory.Mem.Vol
end

