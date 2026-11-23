module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import GroundTheory.AutomorphicForms.Bundle0024
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0290
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0286
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0279
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVanishingIdealSystem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0272
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0267
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealLeThickening

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermBlockMatrix
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SizeCells

theorem exists_perm_cell_sizes : ∀ {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (e' : (Σ j, m' j) ≃ Fin N) (b : SizeMatrix m m'), ∃ w : Equiv.Perm (Fin N), ∀ i j, ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card) = b.1 i j := by
  intro α _ _ N m _ _ β' _ _ m' _ _ e e' b
  obtain ⟨f⟩ := b.nonempty_rows
  obtain ⟨g⟩ := b.nonempty_cols
  let A : (Σ i, Σ j, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  let B : (Σ j, Σ i, Fin (b.1 i j)) ≃ Fin N := (Equiv.sigmaCongrRight g).trans e'
  let S : (Σ i, Σ j, Fin (b.1 i j)) ≃ (Σ j, Σ i, Fin (b.1 i j)) :=
    { toFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      invFun := fun p => ⟨p.2.1, p.1, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let w : Equiv.Perm (Fin N) := (B.symm.trans S.symm).trans A
  have hA : ∀ p, blk e (A p) = p.1 := by
    intro p
    simp [A, blk]
  have hB : ∀ p, blk e' (B p) = p.1 := by
    intro p
    simp [B, blk]
  have hw : ∀ p, w.symm (A p) = B (S p) := by
    intro p
    simp [w]
  refine ⟨w, fun i j => ?_⟩
  have himg : (Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j) =
      Finset.univ.image (fun t : Fin (b.1 i j) => A ⟨i, j, t⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨⟨i', j', t⟩, rfl⟩ := A.surjective x
      rw [hA] at h1
      rw [hw, hB] at h2
      dsimp only [S, Equiv.coe_fn_mk] at h1 h2
      subst h1
      subst h2
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨hA _, ?_⟩
      rw [hw, hB]
      rfl
  rw [himg, Finset.card_image_of_injective _ (fun s t h => by simpa using A.injective h)]
  simp

end GlobalTheory.CompanionTheory.SizeCells
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsXProdPowSmulEqEv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem exists_xProd_pow_smul_eq_ev : ∀ (ι : Type) [LinearOrder ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (b : P (S ∪ T)), S.Nonempty → ∃ l : ℕ, xProd A T ^ l • b ∈ LinearMap.range (res S (S ∪ T) Finset.subset_union_left)) → (∀ (i : ι) (f : P {i}), ∃ (c : ∀ j : ι, P {j}) (N : ℕ), (∀ j l, res {j} {j, l} (sub_pair_left j l) (c j) = res {l} {j, l} (sub_pair_right j l) (c l)) ∧ c i = (MvPolynomial.X i : MvPolynomial ι A) ^ N • f) → ∀ (I : Finset ι) (hI : I.Nonempty) (f : P I), ∃ (l : ℕ) (m : glue res), ev res I hI m = xProd A I ^ l • f := by
  intro ι _ A _ P _ _ _ _ res hcomp hsurj hfam I hI f
  classical
  obtain ⟨i, hi⟩ := hI
  have hsub : ({i} : Finset ι) ⊆ I := Finset.singleton_subset_iff.2 hi
  have key : ∀ (J : Finset ι) (hJ : {i} ∪ I = J) (g : P J),
      ∃ (l : ℕ) (a : P {i}), res {i} J (hJ ▸ Finset.subset_union_left) a = xProd A I ^ l • g := by
    intro J hJ
    subst hJ
    intro g
    obtain ⟨l, a, ha⟩ := hsurj I {i} g ⟨i, Finset.mem_singleton_self i⟩
    exact ⟨l, a, ha⟩
  obtain ⟨l, a, ha⟩ := key I (Finset.union_eq_right.2 hsub) f
  obtain ⟨c, N, hc, hci⟩ := hfam i a
  obtain ⟨q, hq⟩ : (MvPolynomial.X i : MvPolynomial ι A) ∣ xProd A I := by
    simpa [xProd] using Finset.dvd_prod_of_mem (fun j => (MvPolynomial.X j : MvPolynomial ι A)) hi
  refine ⟨N + l, q ^ N • ⟨c, mem_glue.2 hc⟩, ?_⟩
  rw [map_smul, ev_eq hcomp ⟨i, hi⟩ hi]
  change q ^ N • res {i} I hsub (c i) = _
  rw [hci, map_smul, show res {i} I hsub a = xProd A I ^ l • f from ha, hq, smul_smul, smul_smul,
    pow_add, mul_pow]
  congr 1
  ring

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationTransportEquiv
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.FiltTransfer

theorem subQuot_of_filtration : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  intro G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ
  have he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v) := fun h v =>
    e.toIntertwiningMap.isIntertwining _ _ h v
  let S : ℕ → Subrepresentation ρ := fun i =>
    ⟨(Vf i).comap e.toLinearMap, fun h v hv => by
      have hv' : e v ∈ Vf i := hv
      show e (ρ h v) ∈ Vf i
      rw [he]
      exact hV i (ψ h) hv'⟩
  have memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i := fun _ _ => Iff.rfl
  refine ⟨fun t => S t, ?_, ?_, ?_, ?_⟩
  · intro a b hab v hv
    exact hm (Fin.le_def.1 hab) hv
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf 0 ↔ v = 0
    rw [h0]
    simp
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf K ↔ True
    rw [hK]
    simp
  · intro t
    obtain ⟨Ψ, hs, hk⟩ := hΨ t
    let f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t :=
      Ψ.toLinearMap ∘ₗ
        (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)
    have hf : ∀ x, f x = Ψ ⟨e x, x.2⟩ := fun _ => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨w, rfl⟩ := hs y
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · show e (e.symm w) ∈ Vf (t + 1)
        simp
      · rw [hf]
        congr 1
        apply Subtype.ext
        simp
    have hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f := by
      ext x
      rw [LinearMap.mem_ker, hf, hk]
      rfl
    let E := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)
    refine ⟨Representation.Equiv.mk E ?_⟩
    intro g
    have hE : ∀ x, E (Submodule.Quotient.mk x) = f x := fun x => rfl
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ =
        τ t (ψ g) (f x) := by
      rw [hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]
      congr 1
      exact Subtype.ext (he g x)
    exact hstep

end GlobalTheory.CompanionTheory.FiltTransfer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSize
section
noncomputable section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.WedgeSupport

theorem nF_nonneg' {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_nonneg' {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem map_mul_eq_one {R S ι κ : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq κ] (f : R →+* S)
    {A : Matrix ι κ R} {Y : Matrix κ ι R} (h : Y * A = 1) : Y.map f * A.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

theorem one_le_sz_pow_mul_nF (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) :
    1 ≤ sz Y ^ Fintype.card κ * nF A := by
  have h1 := (hF K ι κ κ A).1 Y
  rw [h, (hF K κ κ κ 1).2.2 1, det_one, norm_one] at h1
  exact h1

theorem nF_le_sz_pow (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≤ sz A ^ Fintype.card κ := by
  have h1 := (hF K κ ι κ (1 : Matrix κ κ K)).1 A
  rw [Matrix.mul_one, (hF K κ κ κ 1).2.2 1, det_one, norm_one, mul_one] at h1
  exact h1

theorem nF_ne_zero_of_left_inv (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) : nF A ≠ 0 := by
  intro h0
  have h1 := one_le_sz_pow_mul_nF hF h
  rw [h0, mul_zero] at h1
  linarith

theorem nF_eq_one_of_sz_le (hF : MulF) {K ι κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [Fintype κ]
    [DecidableEq κ] {A : Matrix ι κ K} {Y : Matrix κ ι K} (h : Y * A = 1) (hY : sz Y ≤ 1) (hA : sz A ≤ 1) :
    nF A = 1 := by
  apply le_antisymm
  · exact (nF_le_sz_pow hF A).trans (pow_le_one₀ (sz_nonneg' A) hA)
  · have h1 := one_le_sz_pow_mul_nF hF h
    have h2 : sz Y ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' Y) hY
    nlinarith [nF_nonneg' A]

theorem nI_ne_zero_of_left_inv (hI : MulI) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ ℂ} {Y : Matrix κ ι ℂ} (h : Y * A = 1) : nI A ≠ 0 := by
  intro h0
  have h1 := (hI ι κ κ A).1 Y
  rw [h, (hI κ κ κ 1).2.2 1, det_one, norm_one, h0, mul_zero] at h1
  norm_num at h1

theorem finSupp_of_mul : MulF → MulI → SzFin → FinSupp := by
  intro hF hI hS E _ _ _ ι κ _ _ _ _ A Y h
  refine ⟨fun v => nI_ne_zero_of_left_inv hI (map_mul_eq_one (cV v) h),
    fun w => nF_ne_zero_of_left_inv hF (map_mul_eq_one (cW w) h), ?_⟩
  refine ((hS E κ ι Y).union (hS E ι κ A)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at hn
  exact hw (nF_eq_one_of_sz_le hF (map_mul_eq_one (cW w) h) hn.1 hn.2)

end GlobalTheory.CompanionTheory.WedgeSupport

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotient
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.FlatThick


open TensorProduct in
set_option backward.isDefEq.respectTransparency true in
theorem flat_quotientMap {P B : Type} [CommRing P] [CommRing B] [Algebra P B] [Module.Flat P B] (I₀ : Ideal P) :
    (Ideal.quotientMap (I₀.map (algebraMap P B)) (algebraMap P B) Ideal.le_comap_map :
      P ⧸ I₀ →+* B ⧸ I₀.map (algebraMap P B)).Flat := by
  have f3 : (algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let e₂ : (B ⧸ I₀.map (algebraMap P B)) ≃+* (P ⧸ I₀) ⊗[P] B :=
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).toRingEquiv).trans
        (Algebra.TensorProduct.comm P B (P ⧸ I₀)).toRingEquiv)
  have f5 : (e₂.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₂.symm.bijective
  have f4 := RingHom.Flat.comp f3 f5
  convert f4 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  refine e₂.injective ?_
  have : e₂ (Ideal.Quotient.mk _ (algebraMap P B r)) = algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B) (Ideal.Quotient.mk _ r) := by
    change Algebra.TensorProduct.comm P B (P ⧸ I₀) (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀ (Ideal.Quotient.mk _ (algebraMap P B r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  simpa using this

theorem flat_of_surjective_ker {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (π : A →+* A') (hπ : Function.Surjective π) (a : A) (hker : RingHom.ker π = Ideal.span {a})
    (g : A' →+* B ⧸ Ideal.span {f a}) (hg : ∀ r, g (π r) = Ideal.Quotient.mk _ (f r)) : g.Flat := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hJ : (Ideal.span {a}).map (algebraMap A B) = Ideal.span {f a} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let e₁ : (A ⧸ Ideal.span {a}) ≃+* A' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₂ : (B ⧸ (Ideal.span {a}).map (algebraMap A B)) ≃+* (B ⧸ Ideal.span {f a}) := Ideal.quotEquivOfEq hJ
  have h0 := flat_quotientMap (P := A) (B := B) (Ideal.span {a})
  have h1 : (e₁.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₁.symm.bijective
  have h2 : (e₂.toRingHom).Flat := RingHom.Flat.of_bijective e₂.bijective
  have h3 := RingHom.Flat.comp (RingHom.Flat.comp h1 h0) h2
  convert h3 using 1
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := hπ x
  have hr : e₁.symm (π r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change g (π r) = e₂ (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map (e₁.symm (π r)))
  rw [hr, hg]
  rfl

theorem flatT_qT (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O]
    (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) (hT : FlatT T) :
    FlatT (qT hn T) := by
  refine flat_of_surjective_ker T.i hT (Wc.red l k n) ?_ (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n)) ?_ (qi T)
    (qi_red T)
  · intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, red_mk' w⟩
  · ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, red_mk', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Ideal.Quotient.mk _ c, (map_mul _ _ _)⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨c + (l : WittVector l k) * d, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ, ← hd]
      ring

end GlobalTheory.CompanionTheory.FlatThick

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforward
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem core_integral_step : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hφ : IsProper (ψ ≫ J.subschemeι) := by
    haveI := hψ
    infer_instance
  have hcl := GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS
  have hps := _root_.GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys I (ψ ≫ J.subschemeι) hφ hover hE hS hP
  have hEZ := isCoherent_pullback (ψ ≫ J.subschemeι) hE
  obtain ⟨B, hBq, hBP, hB⟩ := hZ _ hEZ _ hcl (fun e U a ha x => by
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨0, by rw [map_zero, zero_smul]⟩) hps
  have := hEZ.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow hEZ
  have hP' := GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG
  have := hP'.1
  have hE1 := hE.1
  have hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm
      (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.GE.Shift.shift I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.CompanionTheory.GE.Globalize.exists_uniform_pow_kills hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀
    (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)
  refine ⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq,
    GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))
  · intro n U a ha x hx
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul]
    obtain ⟨y, rfl⟩ := hx
    exact (secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.TwGen

variable {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}

def genHom (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n) ⟶ P :=
  GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) ≫
    (GlobalTheory.Twist.twistZAddIso P hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso P hH).inv

def genSub (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) : Subobject P :=
  imageSubobject (genHom hH n b)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedProj
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := _root_.GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.T.homogeneous_lift_adic_filtration R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact _root_.GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothCompContinuous
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.SmoothBridge

theorem isSmooth_comp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (ψ : H →* G) (hψ : Continuous ψ) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (hρ : GlobalTheory.PRep.IsSmooth ρ) : GroundTheory.Automorphic.IsSmooth (ρ.comp ψ) := by
  intro v
  have h := (hρ v).preimage hψ
  exact h

end GlobalTheory.CompanionTheory.SmoothBridge
end

