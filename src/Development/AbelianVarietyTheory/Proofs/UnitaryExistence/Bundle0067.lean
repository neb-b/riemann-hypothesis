module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
section
noncomputable section

namespace GlobalTheory.UnitaryGlue

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_map {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) (s : R →+* R) (t : A →+* A)
    (h : ∀ z, p (s z) = t (p z)) (M : Matrix n n R) :
    (Formalism.UG.cT s M).map p = Formalism.UG.cT t (M.map p) := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem exists_glue {ι R : Type} [CommRing R] {A : ι → Type} [∀ i, CommRing (A i)] (p : ∀ i, R →+* A i)
    (hp : Function.Bijective fun (z : R) (i : ι) => p i z) (s : R →+* R) (t : ∀ i, A i →+* A i)
    (h : ∀ i z, p i (s z) = t i (p i z)) (J : Matrix n n R) (g : ∀ i, GL n (A i))
    (hg : ∀ i, g i ∈ Formalism.UG.UJ (t i) (J.map (p i))) :
    ∃ x ∈ Formalism.UG.UJ s J, ∀ i, Formalism.UG.bc (p i) x = g i := by
  have inj : ∀ M N : Matrix n n R, (∀ i, M.map (p i) = N.map (p i)) → M = N := by
    intro M N hMN
    ext a b
    exact hp.1 (funext fun i => congrFun (congrFun (hMN i) a) b)
  have sur : ∀ u : ∀ i, Matrix n n (A i), ∃ M : Matrix n n R, ∀ i, M.map (p i) = u i := by
    intro u
    choose M hM using fun a b => hp.2 (fun i => u i a b)
    exact ⟨Matrix.of M, fun i => by ext a b; exact congrFun (hM a b) i⟩
  obtain ⟨M, hM⟩ := sur fun i => (g i).1
  obtain ⟨N, hN⟩ := sur fun i => ((g i)⁻¹).1
  have h1 : ∀ i, (1 : Matrix n n R).map (p i) = 1 := fun i => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ fun i => ?_, inj _ _ fun i => ?_⟩, ?_, fun i => Units.ext (hM i)⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (p i) s (t i) (h i), hM]
    exact hg i

theorem exists_glue₂ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (p : R →+* A) (q : R →+* B)
    (e : R ≃+* A × B) (he : ∀ z, (e z).1 = p z ∧ (e z).2 = q z) (s : R →+* R) (t : A →+* A) (t' : B →+* B)
    (h : ∀ z, p (s z) = t (p z)) (h' : ∀ z, q (s z) = t' (q z)) (J : Matrix n n R) (g : GL n A) (g' : GL n B)
    (hg : g ∈ Formalism.UG.UJ t (J.map p)) (hg' : g' ∈ Formalism.UG.UJ t' (J.map q)) :
    ∃ x ∈ Formalism.UG.UJ s J, Formalism.UG.bc p x = g ∧ Formalism.UG.bc q x = g' := by
  have inj : ∀ M N : Matrix n n R, M.map p = N.map p → M.map q = N.map q → M = N := by
    intro M N h1 h2
    ext a b
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 a) b
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 a) b
  have sur : ∀ (u : Matrix n n A) (v : Matrix n n B), ∃ M : Matrix n n R, M.map p = u ∧ M.map q = v := by
    intro u v
    refine ⟨Matrix.of fun a b => e.symm (u a b, v a b), ?_, ?_⟩
    · ext a b
      simp [← (he _).1]
    · ext a b
      simp [← (he _).2]
  obtain ⟨M, hM, hM'⟩ := sur g.1 g'.1
  obtain ⟨N, hN, hN'⟩ := sur (g⁻¹).1 (g'⁻¹).1
  have h1 : (1 : Matrix n n R).map p = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (1 : Matrix n n R).map q = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ ?_ ?_, inj _ _ ?_ ?_⟩, ?_, Units.ext hM, Units.ext hM'⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM', hN', h2, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · rw [Matrix.map_mul, hM', hN', h2, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map p s t h, hM]
      exact hg
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map q s t' h', hM']
      exact hg'

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : ∀ i, V.hT (V.frame i) (V.frame.equivFun.symm v) = 0 := by
    intro i
    have := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have h2 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← V.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  exact hv (V.frame.equivFun.symm.injective (h2.trans (map_zero _).symm))

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ z) =
      sigR S σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_map_inclR (f : R →ₐ[F] S) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (J.map (inclR R)).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = J.map (inclR S) := by
  ext i j
  simp [inclR]

end Tens

theorem exists_inf_fin {D : D7} (V : HSp D) (gi : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hi : gi ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram) (hf : gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) :
    ∃ g : GA D V, infHom V g = gi ∧ finHom V g = gf := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨x, hx, h1, h2⟩ := exists_glue₂
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom e he
    (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (map_sigR _ _) (map_sigR _ _)
    (JR (AF D.host.F) V.gram) gi gf
    (by rw [JR, map_map_inclR]; exact hi) (by rw [JR, map_map_inclR]; exact hf)
  exact ⟨⟨x, hx⟩, h1, h2⟩

theorem adelic_glue : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  intro D V
  letI := D.host.cmStar
  refine ⟨fun gf hf => ?_, fun Ψ th hΨ hth => ?_⟩
  · obtain ⟨g, h1, h2⟩ := exists_inf_fin V 1 gf (one_mem _) hf
    exact ⟨g, h1, h2⟩
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  have hτ : ∀ (τ : D.host.E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : c ≠ 1 := fun h => IsCMField.complexConj_ne_one D.host.E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
  obtain ⟨hex, hall⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E c D.sp.cm.deg2 hc
    D.sp.cm.totReal hτ
  choose θ₀ hθ₀ using hex
  classical
  let θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :=
    fun τ => if h : τ ∈ Ψ then th ⟨τ, h⟩ else θ₀ τ
  have hθt : ∀ τ : Ψ, θ τ.1 = th τ := fun τ => dif_pos τ.2
  obtain ⟨hcont, hconj, hbij⟩ := hall θ (fun τ => by
    by_cases h : τ ∈ Ψ
    · rw [hθt ⟨τ, h⟩]; exact hth ⟨τ, h⟩
    · have : θ τ = θ₀ τ := dif_neg h
      rw [this]; exact hθ₀ τ)
  have hb : Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z := by
    have := hbij (Ψ : Set _) hΨ
    have e : (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z) =
        fun z (τ : Ψ) => θ τ.1 z := by
      funext z τ; rw [hθt]
    rw [e]; exact this
  have hinc : ∀ (τ : Ψ) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      (M.map (inclR (Ainf D.host.F))).map (th τ) = M.map τ.1 := by
    intro τ M
    ext i j
    exact (hth τ).1 _
  refine ⟨fun g hg => ?_, fun γ hγ => ?_, fun τ => ?_, fun u hu => ?_⟩
  · refine Units.ext (Matrix.ext fun a b => hb.1 (funext fun τ => ?_))
    have h1 := congrFun (congrFun (hg τ) a) b
    have h2 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).map (th τ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    exact h1.trans (congrFun (congrFun h2 a) b).symm
  · obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have h1 : (matHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (AF D.host.F)) :=
      (congrArg Units.val h0).symm
    refine ⟨γ₀, fun τ => ?_, ?_⟩
    · rw [← hinc, ← map_map_inclR (fstA D.host.F), ← h1]; rfl
    · rw [← map_map_inclR (sndA D.host.F), ← h1]; rfl
  · obtain ⟨e, he, hec, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous (th τ) := hθt τ ▸ hcont τ.1
    have h2 : Continuous fun g : GA D V => (matHom V g).1 a b :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b
    have h3 : (fun g : GA D V => archM V (th τ) g a b) = fun g => th τ (e ((matHom V g).1 a b)).1 := by
      funext g
      rw [(he _).1]; rfl
    rw [h3]
    exact h1.comp (continuous_fst.comp (hec.comp h2))
  · have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact gram_det_ne_zero V (τ.1.injective (by rw [map_zero, this]))
    obtain ⟨x, hx, hxu⟩ := exists_glue (A := fun _ : Ψ => ℂ) th hb (sigR _ D.sp.cm.sig) (fun _ => starRingEnd ℂ)
      (fun τ z => hθt τ ▸ hconj τ.1 z) (JR (Ainf D.host.F) V.gram)
      (fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (u τ) (hdet τ))
      (fun τ => by rw [JR, hinc]; exact hu τ)
    obtain ⟨g, h1, h2⟩ := exists_inf_fin V x 1 hx (one_mem _)
    refine ⟨g, h2, fun τ => ?_⟩
    rw [archM, h1]
    exact congrArg Units.val (hxu τ)

end GlobalTheory.UnitaryGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DatumSum

noncomputable section

def blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (f.prodMap g) ∘ₗ e.toLinearMap

theorem blockEnd_apply {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) (x : U) :
    e (blockEnd e f g x) = (f (e x).1, g (e x).2) := by
  simp [blockEnd, Prod.map]

theorem blockEnd_comp {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (e : U ≃ₗ[ℝ] V × W) (f f' : V →ₗ[ℝ] V) (g g' : W →ₗ[ℝ] W) :
    blockEnd e f g ∘ₗ blockEnd e f' g' = blockEnd e (f ∘ₗ f') (g ∘ₗ g') := by
  ext x
  apply e.injective
  simp [blockEnd_apply]

theorem trace_blockEnd {U V W : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] [Module.Finite ℝ V] [Module.Finite ℝ W] (e : U ≃ₗ[ℝ] V × W) (f : V →ₗ[ℝ] V) (g : W →ₗ[ℝ] W) :
    LinearMap.trace ℝ U (blockEnd e f g) = LinearMap.trace ℝ V f + LinearMap.trace ℝ W g := by
  have h1 : blockEnd e f g = e.symm.conj (f.prodMap g) := by
    ext x; simp [blockEnd, LinearEquiv.conj_apply]
  rw [h1, LinearMap.trace_conj', LinearMap.trace_prodMap']

def sumForm {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) : LinearMap.BilinForm ℤ (L × M) :=
  B.compl₁₂ (LinearMap.fst ℤ L M) (LinearMap.fst ℤ L M) + C.compl₁₂ (LinearMap.snd ℤ L M) (LinearMap.snd ℤ L M)

theorem sumForm_apply {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : L × M) : sumForm B C x y = B x.1 y.1 + C x.2 y.2 := by
  simp [sumForm]

theorem sumForm_bijective {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) (hC : Function.Bijective C) :
    Function.Bijective (sumForm B C) := by
  constructor
  · intro x y h
    refine Prod.ext (hB.1 ?_) (hC.1 ?_)
    · ext z
      have := LinearMap.congr_fun h (z, 0)
      simpa [sumForm_apply] using this
    · ext z
      have := LinearMap.congr_fun h (0, z)
      simpa [sumForm_apply] using this
  · intro φ
    obtain ⟨x, hx⟩ := hB.2 (φ ∘ₗ LinearMap.inl ℤ L M)
    obtain ⟨y, hy⟩ := hC.2 (φ ∘ₗ LinearMap.inr ℤ L M)
    refine ⟨(x, y), LinearMap.ext fun z => ?_⟩
    rw [sumForm_apply, hx, hy]
    simp [← map_add (f := _)]

theorem sumForm_baseChange {L M : Type} [AddCommGroup L] [AddCommGroup M] (B : LinearMap.BilinForm ℤ L)
    (C : LinearMap.BilinForm ℤ M) (x y : ℝ ⊗[ℤ] (L × M)) :
    (sumForm B C).baseChange ℝ x y =
      B.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).1 (TensorProduct.prodRight ℤ ℝ ℝ L M y).1 +
      C.baseChange ℝ (TensorProduct.prodRight ℤ ℝ ℝ L M x).2 (TensorProduct.prodRight ℤ ℝ ℝ L M y).2 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, Prod.fst_add, Prod.snd_add, ha, hb]; ring
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, ha, hb]; ring
    | tmul s v => simp [sumForm_apply, add_smul, add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sumDatum (D D' : Datum H) : Datum H where
  La := D.La × D'.La
  fin := by haveI := D.fin; haveI := D'.fin; infer_instance
  proj := by haveI := D.proj; haveI := D'.proj; infer_instance
  EF := sumForm D.EF D'.EF
  alt := fun x => by simp [sumForm_apply, D.alt, D'.alt]
  unimod := sumForm_bijective D.EF D'.EF D.unimod D'.unimod
  adj := fun a x y => by simp [sumForm_apply, D.adj, D'.adj]
  p := D.p + D'.p
  q := D.q + D'.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    haveI := D'.fin
    haveI := D'.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (D.La × D'.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h2' := (TensorProduct.isBaseChange (𝓞 E) D'.La E).finrank_eq
    have h3 := (TensorProduct.prodRight (𝓞 E) E E D.La D'.La).finrank_eq
    rw [← h1, h3, Module.finrank_prod, h2, h2', D.rank, D'.rank]
    ring
  dom := by
    haveI := D.fin
    haveI := D'.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) D'.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    obtain ⟨J', h1', h2', h3', h4'⟩ := D'.dom
    set e := TensorProduct.prodRight ℤ ℝ ℝ D.La D'.La with he
    refine ⟨blockEnd e J J', ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      simp [blockEnd_apply, h1, h1', Prod.ext_iff]
    · intro x y
      simp only [sumForm_baseChange, ← he, blockEnd_apply, h2, h2']
    · intro x hx
      simp only [sumForm_baseChange, ← he, blockEnd_apply]
      have hne : e x ≠ 0 := fun hc => hx (e.injective (by rw [map_zero]; exact hc))
      by_cases ha : (e x).1 = 0
      · have hb : (e x).2 ≠ 0 := fun hb => hne (Prod.ext ha hb)
        simpa [ha] using h3' _ hb
      · by_cases hb : (e x).2 = 0
        · simpa [hb] using h3 _ ha
        · exact add_pos (h3 _ ha) (h3' _ hb)
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribSMul.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      let A1 : ℝ ⊗[ℤ] D'.La →ₗ[ℝ] ℝ ⊗[ℤ] D'.La :=
        ((DistribSMul.toAddMonoidHom D'.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      obtain ⟨k1', k2', k3'⟩ := h4' a A1 _ (fun x => by simp [A1]) rfl
      have hAA : A = blockEnd e A0 A1 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          rw [blockEnd_apply]
          simp [he, A0, A1]
      have ht' : t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) +
          ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
          ((D'.p : ℂ) * τ (a : E) + (D'.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, blockEnd_comp, blockEnd_comp, trace_blockEnd, trace_blockEnd, k1, ← k1, k1', ← k1', k2, k3, k2', k3',
        ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.add_re]; ring
      · rw [Complex.add_im]; ring

end

end GlobalTheory.DatumSum

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem tan_bc {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap, dualMap_comp_alg, ← spMap_comp_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem eig_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z := by
  intro hB E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  obtain ⟨s', hs', -⟩ := _root_.GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo S T φ.toRingHom 1 y.x (spMap φ.toRingHom ≫ y.x) rfl y.s
  have hnz : SecNZ y.x y.s := _root_.GlobalTheory.Frames.secNZ_of_secGen hB E H Dw l Xo S y.x y.s y.gen
  have hnz' : SecNZ (spMap φ.toRingHom ≫ y.x) s' := fun p' =>
    (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S T φ.toRingHom y.x _ rfl y.s s' hs' p').2 (hnz _)
  have hgen : SecGen (spMap φ.toRingHom ≫ y.x) s' := _root_.GlobalTheory.Frames.secGen_of_secNZ hB E H Dw l Xo T _ s' hnz'
  refine ⟨{ x := spMap φ.toRingHom ≫ y.x
            x_over := ?_
            u := fun τ i => spMap (dualMap φ.toRingHom) ≫ y.u τ i
            tan := fun τ i => tan_bc φ.toRingHom (y.tan τ i)
            eig := fun τ i => eig_bc φ τ (y.eig τ i)
            basis := fun τ w hw he => _root_.GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c S T φ y τ w hw he
            s := s'
            gen := hgen }, rfl, fun _ _ => rfl, ?_⟩
  · rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  · obtain ⟨pm, h1, h2, h3⟩ := hs'
    refine ⟨pm, h1, h2, fun i h => ?_⟩
    have h4 := h3 i h
    have h5 : scal y.x (1 : S) i = 1 := by
      unfold scal
      rw [map_one]
      simp [Out.liftFun]
    rw [h5, _root_.one_mul] at h4
    exact h4

end GlobalTheory.Frames.FramedBaseChange
end

