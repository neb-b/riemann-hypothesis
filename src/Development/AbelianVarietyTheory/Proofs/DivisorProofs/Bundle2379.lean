module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivCond_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  intro S A _ N hA hN hR T t hloc Y φ y hY
  haveI := hA.comm
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  let e : Over.mk y ≅ (Over.pullback t).obj A := Over.isoMk hY.isoPullback hY.isoPullback_hom_snd
  letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk y) A t φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _)
      (by simp [e])
  have hA' : IsAbelianScheme (Over.mk y) := by
    refine ⟨?_, MorphismProperty.of_isPullback (P := @Smooth) hP.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hP.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hP.1 hA.geomConnected⟩
    rw [isCommMonObj_iff_isMulCommutative]
    intro U
    refine ⟨⟨fun x z => Over.OverMorphism.ext (hP.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
    rw [← hP.2 U x z (pushPt hP.1.w x) (pushPt hP.1.w z) rfl rfl,
      ← hP.2 U z x (pushPt hP.1.w z) (pushPt hP.1.w x) rfl rfl, _root_.mul_comm]
  haveI := hA'.comm
  obtain ⟨r, hr⟩ := hR
  have he : eSec (Over.mk y) ≫ φ = t ≫ eSec A := (cubeMapOf hP).e_comm
  have g := rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr
  have hR' : Out.Rigidified (Over.mk y) (N.pull φ) := ⟨_, g⟩
  refine _root_.GlobalTheory.RigTriv.exists_gen_of_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)
  obtain ⟨V, hτ, hV⟩ := hloc τ
  refine ⟨V, hτ, ?_⟩
  have H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t) :=
    (isPullback_morphismRestrict y V).flip.paste_horiz hY
  exact (GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)

end GlobalTheory.TrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryAction
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.KSplit.om_linW_split : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (g, h)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) (locMat t b g) (locMat t c h) (ι φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t b c ι hι g hg h hh φ hφ φ₁ hφ₁ hA
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hp v
  have oneX : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    simp [mat]
  have oneW : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  have hspl := hp.weil.isUSplitting
  obtain ⟨φ', ⟨hφ', hA'⟩, -⟩ := hex 1 oneX h hh φ hφ
  obtain ⟨φ'', ⟨hφ'', hA''⟩, -⟩ := hex g hg 1 oneW φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R := ⟨hR.1, by rw [← hA' R hR]; exact hspl.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι
  have sW := GlobalTheory.T.linear_model_compact_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κW hW h hh
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B n d X W M χX χW om r s r' s' hp v t b c ι hι κX hX g hg
  rw [e1, hX g hg φ' hφ' φ'' hφ'' hA'', hW h hh φ hφ φ' hφ' hA', sW, sX]
  funext Y
  simp only [GlobalTheory.SplitFlip.omA, Pi.smul_apply, smul_eq_mul, Fintype.card_fin, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, inv_inv, Matrix.mul_assoc]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingGraphGenericPointOfInjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair


open GlobalTheory.DiagLoc in
theorem localRing_graph_of_injective : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  Function.Injective π → (∀ g : K, ∃ a b : R, (b : K) ≠ 0 ∧ g * b = a) →
  IsLocModel (algebraMap ℂ K) R → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → 1 ≤ k →
  ∃ (Q : Subring L) (hQ : IsLocModel (algebraMap ℂ L) Q), letI := hQ.isLocalRing; ∃ z : Fin k → Q,
    IsLocalRing.maximalIdeal Q = Ideal.span (Set.range z) ∧ ringKrullDim Q = k ∧
    (∀ g : K, g ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) ∧
    (∀ b : κ', b ≠ 0 → ∃ q : Q, IsUnit q ∧ (q : L) = algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      ∃ q : Q, IsUnit q ∧ (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) ∧
    (∀ (M l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M →
      ∃ q : Q, (q : L) = (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ∧ q ∈ IsLocalRing.maximalIdeal Q ^ M) ∧
    ∃ (y : Fin (k' + n) → Q) (q : Q), IsFreeGen Q (dForm ((algebraMap ℂ L).codRestrict Q hQ.const_mem) y) ∧ IsUnit q ∧
      dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
        (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1))) = (q : L) • dForm (algebraMap ℂ L) (fun i => (y i : L)) := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ' hz hπc hπf hπi hRf hR hκ' hk
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locModel_fracField_algEquiv R π hR hπc hπf hπi
  obtain ⟨z, hz⟩ := hz
  obtain rfl : n = k := _root_.GlobalTheory.trBasis_card_eq_of_algEquiv e n k x z hx hz
  have hK : Algebra.EssFiniteType ℂ K := _root_.GlobalTheory.essFiniteType_of_isLocModel R hR
  obtain ⟨O', hO'⟩ := hκ'
  have hκ'f : Algebra.EssFiniteType ℂ κ' := _root_.GlobalTheory.essFiniteType_of_isLocModel O' hO'
  set σ : K →ₐ[ℂ] κ' := ρ.comp e.toAlgHom with hσ
  have hQ : IsLocModel (algebraMap ℂ L) (loc L σ) := _root_.GlobalTheory.DiagLoc.isLocModel_loc σ hK hκ'f
  obtain ⟨hm, hdim⟩ := _root_.GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim (L := L) σ n x hK hκ'f hx
  have hsum : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      algebraMap (K ⊗[ℂ] κ') L (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i) := fun l a b => map_sum _ _ _
  have hprod : ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'),
      Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') (∑ i, (a i : K) ⊗ₜ[ℂ] b i) =
        ∑ i, ρ (π (a i)) * b i := by
    intro l a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, σ, he]
  refine ⟨loc L σ, hQ, fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i)), hm, hdim, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    refine ⟨toLoc L σ (g ⊗ₜ 1), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 g hg).map (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ) (B := κ')))
  · intro b hb
    refine ⟨toLoc L σ (1 ⊗ₜ b), ?_, rfl⟩
    refine IsUnit.map _ ?_
    exact ((IsUnit.mk0 b hb).map (Algebra.TensorProduct.includeRight (R := ℂ) (A := K)))
  · intro l a b hne
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), ?_, ?_⟩
    · have hs : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ (ker σ).primeCompl := by
        intro hmem
        exact hne ((hprod l a b).symm.trans hmem)
      exact IsLocalization.map_units (loc L σ) (⟨_, hs⟩ : (ker σ).primeCompl)
    · simp only [coe_toLoc]
      exact hsum l a b
  · intro M l a b hJ
    refine ⟨toLoc L σ (∑ i, (a i : K) ⊗ₜ[ℂ] b i), by simp only [coe_toLoc]; exact hsum l a b, ?_⟩
    let E : K ⊗[ℂ] κ' ≃ₐ[ℂ] κ ⊗[ℂ] κ' := Algebra.TensorProduct.congr e AlgEquiv.refl
    have hE : (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')).comp E.toAlgHom =
        Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') := by
      apply Algebra.TensorProduct.ext'
      intro g b
      simp [E, σ]
    have hker : ker σ = (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
        (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') := by
      ext s
      simp only [mem_ker, Ideal.mem_comap, RingHom.mem_ker]
      rw [← hE]
      rfl
    have hEs : E (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = ∑ i, π (a i) ⊗ₜ[ℂ] b i := by
      simp [E, he]
    have hmem : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) ∈ ker σ ^ M := by
      have h1 : (∑ i, (a i : K) ⊗ₜ[ℂ] b i) = E.symm (∑ i, π (a i) ⊗ₜ[ℂ] b i) := by
        rw [← hEs, AlgEquiv.symm_apply_apply]
      have h2 := Ideal.mem_map_of_mem (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') hJ
      have h3 : (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).comap
          (E : K ⊗[ℂ] κ' →+* κ ⊗[ℂ] κ') =
          (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))).map
          (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ') := by
        ext s
        rw [Ideal.mem_comap, Ideal.mem_map_iff_of_surjective (E.symm : κ ⊗[ℂ] κ' →+* K ⊗[ℂ] κ')
          E.symm.surjective]
        constructor
        · intro hs
          exact ⟨E s, hs, by simp⟩
        · rintro ⟨t, ht, rfl⟩
          simpa using ht
      rw [h1, hker, h3, ← Ideal.map_pow]
      exact h2
    have := Ideal.mem_map_of_mem (toLoc L σ) hmem
    rw [Ideal.map_pow, map_ker] at this
    exact this
  · refine ⟨_, 1, _root_.GlobalTheory.DiagLoc.isFreeGen_dForm_graph σ n k' x τ' hQ.const_mem hK hκ'f hx hτ', isUnit_one, ?_⟩
    rw [Submonoid.coe_one, one_smul]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountNearbyPowersSecondBundleLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_mono_radius {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) (a b : ℤ) {R R' : ℝ} (h : R ≤ R') : P.lc a b R ≤ P.lc a b R' := by
  have hsub : P.Bl a b R ⊆ P.Bl a b R' := fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h⟩
  have hfin : (P.Bl a b R').Finite := _root_.GlobalTheory.HSNef.bl_finite k X p D hX P a b R'
  have hle : (P.Bl a b R).ncard ≤ (P.Bl a b R').ncard := Set.ncard_le_ncard hsub hfin
  unfold VolBr.Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl a b R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

theorem lc_nearby_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
      P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b c hb hR ε hε
  obtain ⟨α, β, hαβ⟩ := hR
  refine GlobalTheory.eventually_le_at_nearby_indices (D + 1) b c
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 j 2) (fun j => P.lc 0 j 1) α β
    (Nat.succ_pos D) hb hαβ ?_ ?_ ε hε
  · intro j
    simp
  · intro η hη
    have ht : Tendsto (fun j : ℕ => Real.exp (η * j)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (eventually_ge_atTop 2)] with j hj
    exact lc_mono_radius hX P 0 (j : ℤ) hj

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_one_eventually_ge : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  intro hA k _ X _ p D hD P a b a' b' M α hRep hAmp hSP hSI ε hε
  obtain ⟨t₀, ht⟩ := _root_.GlobalTheory.HSNef.ampleHS_pair hA k X p D hD P a b a' b' M α hRep hAmp hSP hSI
  exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge X.functionField
    (fun m : ℕ => P.H (m * a + a') (m * b + b')) (fun m : ℕ => P.Bl (m * a + a') (m * b + b')) (D + 1)
    (Nat.succ_pos D) (fun m => GlobalTheory.VolBr.Pair.isBallFam k X p P _ _)
    (fun m R => _root_.GlobalTheory.HSNef.bl_finite k X p D hD P _ _ R) _ _ t₀ ht ε hε

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountTwistExpRadiusLePowSucc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_twist_le_of_good {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {D b : ℕ} {s t : X.functionField} (hG : P.Good D b s t) (N c : ℕ) (R : ℝ)
    (hfin : (P.Bl 0 ((N : ℤ) * b) R).Finite) :
    P.lc N (-c) R ≤ P.lc 0 ((N : ℤ) * b) R := by
  have nu_nonneg : ∀ (a e : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField), 0 ≤ P.nu a e σ y f :=
    fun a e σ y f => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨htH, htn⟩ := hG.t_mem
  obtain ⟨hsH, hsn⟩ := hG.s_mem
  obtain ⟨hpH, hpn⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (-1) b t htH N
  obtain ⟨hqH, hqn⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P 0 1 s hsH c
  have e1 : (N : ℤ) + N * -1 + c * 0 = 0 := by ring
  have e2 : -(c : ℤ) + N * b + c * 1 = N * b := by ring
  have hmaps : ∀ f ∈ P.Bl N (-c) R, f * t ^ N * s ^ c ∈ P.Bl 0 ((N : ℤ) * b) R := by
    rintro f ⟨hfH, hfn⟩
    obtain ⟨hH1, hn1⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P N (-c) (N * -1) (N * b) f (t ^ N) hfH hpH
    obtain ⟨hH, hn⟩ := _root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P (N + N * -1) (-c + N * b) (c * 0) (c * 1) (f * t ^ N) (s ^ c) hH1 hqH
    rw [e1, e2] at hH hn
    refine ⟨hH, fun σ y => ?_⟩
    rw [hn σ y, hn1 σ y, hpn σ y, hqn σ y]
    have h1 : P.nu (-1) b σ y t ^ N ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (htn σ y)
    have h2 : P.nu 0 1 σ y s ^ c ≤ 1 := pow_le_one₀ (nu_nonneg _ _ _ _ _) (hsn σ y)
    have h3 : P.nu N (-c) σ y f * P.nu (-1) b σ y t ^ N ≤ R :=
      (mul_le_of_le_one_right (nu_nonneg _ _ _ _ _) h1).trans (hfn σ y)
    exact (mul_le_of_le_one_right (mul_nonneg (nu_nonneg _ _ _ _ _) (pow_nonneg (nu_nonneg _ _ _ _ _) _)) h2).trans h3
  have hinj : Set.InjOn (fun f => f * t ^ N * s ^ c) (P.Bl N (-c) R) := fun x _ y _ h =>
    mul_right_cancel₀ (pow_ne_zero N hG.t_ne) (mul_right_cancel₀ (pow_ne_zero c hG.s_ne) h)
  have hcard := Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin
  unfold Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl N (-c) R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)

theorem crude_upper_lc_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b s t hG c hR
  obtain ⟨α, β, hαβ⟩ := hR
  have hb : (0 : ℝ) < b := by exact_mod_cast hG.pos
  have hlim := hαβ (3 / b) (by positivity)
  have hsub : Tendsto (fun N : ℕ => b * N) atTop atTop :=
    tendsto_id.const_mul_atTop' hG.pos
  obtain ⟨C, hev⟩ : ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      P.lc 0 ((b * N : ℕ) : ℤ) (Real.exp (3 / b * ((b * N : ℕ) : ℝ))) / ((b * N : ℕ) : ℝ) ^ (D + 1) < C :=
    ⟨_, (hlim.comp hsub).eventually (gt_mem_nhds (lt_add_one _))⟩
  refine ⟨C * (b : ℝ) ^ (D + 1), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have e1 : 3 / (b : ℝ) * ((b * N : ℕ) : ℝ) = 3 * N := by push_cast; field_simp
  have e2 : ((b * N : ℕ) : ℤ) = (N : ℤ) * b := by push_cast; ring
  have hpos : (0 : ℝ) < ((b * N : ℕ) : ℝ) ^ (D + 1) := by push_cast; positivity
  rw [e1, e2, div_lt_iff₀ hpos] at hN
  calc P.lc N (-c) (Real.exp (3 * N)) ≤ P.lc 0 ((N : ℤ) * b) (Real.exp (3 * N)) :=
        lc_twist_le_of_good P hG N c _ (_root_.GlobalTheory.HSNef.bl_finite k X p D hX P 0 _ _)
    _ ≤ C * ((b * N : ℕ) : ℝ) ^ (D + 1) := hN.le
    _ = C * (b : ℝ) ^ (D + 1) * (N : ℝ) ^ (D + 1) := by push_cast; ring

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
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
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem dlog_of_mul_eq {B : Type} [CommRing B] (a₁ a₂ l g : DualNumber B) (i₁ i₂ il ig : B)
    (h : a₁ * l = g * a₂) (h₁ : a₁.fst * i₁ = 1) (h₂ : a₂.fst * i₂ = 1) (hl : l.fst * il = 1)
    (hg : g.fst * ig = 1) : g.snd * ig = l.snd * il + (a₁.snd * i₁ - a₂.snd * i₂) := by
  have h0 : a₁.fst * l.fst = g.fst * a₂.fst := by simpa using congrArg TrivSqZeroExt.fst h
  have h1 : a₁.fst * l.snd + a₁.snd * l.fst = g.fst * a₂.snd + g.snd * a₂.fst := by
    have := congrArg TrivSqZeroExt.snd h
    rwa [DualNumber.snd_mul, DualNumber.snd_mul] at this
  have e1 : a₁.fst * ig * i₂ = il := by
    linear_combination (ig * i₂ * il) * h0 - (a₁.fst * ig * i₂) * hl + (a₂.fst * i₂ * il) * hg + il * h₂
  have e2 : l.fst * ig * i₂ = i₁ := by
    linear_combination (ig * i₂ * i₁) * h0 - (l.fst * ig * i₂) * h₁ + (a₂.fst * i₂ * i₁) * hg + i₁ * h₂
  linear_combination (-(ig * i₂)) * h1 + l.snd * e1 + a₁.snd * e2 - (a₂.snd * i₂) * hg - (g.snd * ig) * h₂

theorem valR_fst_mul_inv {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (u : Γ(Y, O)ˣ) :
    (valR w O u.val).fst * valR x O u⁻¹.val = 1 := by
  have h' := le_preimage_of_red hw h
  subst hw
  have e : (valR w O u.val).fst = ev _ O h u.val := by
    rw [valR_eq_ev _ _ h', GlobalTheory.FlagMod.ev_spMap _ w O h']
    rfl
  rw [e, valR_eq_ev _ _ h, ← map_mul, Units.mul_inv, map_one]

theorem valR_iso_compat {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M)
    (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {S : Type} [CommRing S] (z : Sp S ⟶ Y)
    (h₁ : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ z ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))) :
    valR z _ (wg.s (p₁, fun _ => j₁)).val * valR (z ≫ m) _ (L.g j₁ j₂).val =
      valR z _ (M.g p₁ p₂).val * valR z _ (wg.s (p₂, fun _ => j₂)).val := by
  have e := hwg (p₁, fun _ => j₁) (p₂, fun _ => j₂)
  have hz := GlobalTheory.FlagMod.le_preimage_inf h₁ h₂
  have hP : ⊤ ≤ z ⁻¹ᵁ ((L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂)) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₂)
  have hM : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hle : (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) ≤ m ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit))
  have hg : (L.pull m).g (fun _ => j₁) (fun _ => j₂) = res hle (pullU m _ (L.g j₁ j₂)) := by
    show ∏ _k : PUnit, (res hle (pullU m _ (L.g j₁ j₂))) ^ (1 : ℤ) = _
    simp
  have hl : valR (z ≫ m) _ (L.g j₁ j₂).val = valR z _ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)).val := by
    rw [hg, valR_comp_app]
    exact (valR_resG z hle hP _).symm
  rw [hl]
  have hle₁ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤ M.U p₁ ⊓ M.U p₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hle₂ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤
      (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have e' : res (U := M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) inf_le_left (wg.s (p₁, fun _ => j₁)) =
      res hle₁ (M.g p₁ p₂) * (res hle₂ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)))⁻¹ *
        res (U := M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) inf_le_right (wg.s (p₂, fun _ => j₂)) := e
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at e'
  have e2 := congrArg (fun u : Γ(Y, _)ˣ => ev z _ hz u.val) e'
  simp only [Units.val_mul, map_mul] at e2
  rw [← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev] at e2
  exact (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)).symm.trans
    (e2.trans (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)))

theorem dlog_transition_iso : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  intro Y Z m L M wg hwg j₁ j₂ p₁ p₂ B _ x w hwx h₁ h₂
  have hM : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hL : ⊤ ≤ (x ≫ m) ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    GlobalTheory.FlagMod.le_preimage_inf
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit)) h₁)
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit)) h₂)
  have hwm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (w ≫ m) = x ≫ m := by
    rw [← Category.assoc, hwx]
  exact dlog_of_mul_eq _ _ _ _ _ _ _ _
    (valR_iso_compat m L M wg hwg j₁ j₂ p₁ p₂ w (le_preimage_of_red hwx h₁) (le_preimage_of_red hwx h₂))
    (valR_fst_mul_inv hwx h₁ _) (valR_fst_mul_inv hwx h₂ _) (valR_fst_mul_inv hwm hL _) (valR_fst_mul_inv hwx hM _)

end GlobalTheory.CechKS
end

