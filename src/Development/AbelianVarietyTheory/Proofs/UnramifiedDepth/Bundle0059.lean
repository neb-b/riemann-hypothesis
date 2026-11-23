module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SquarefreeMapMinpolyInt
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SplittingIdempotents

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  first | exact @GlobalTheory.ChF.bxChart_of_nilChart | exact GlobalTheory.ChF.bxChart_of_nilChart | (intros; apply GlobalTheory.ChF.bxChart_of_nilChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualNumberPointPreimageTopOfReduction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma dualNumberPoint_preimage_top_of_reduction {O : Type} [CommRing O] {d r g m : ℕ} (A : Matrix (Fin d) (Fin r) O)
    (B : Matrix (Fin g) (Fin d) O) (h : SplitEx A B) (s : Fin m → Fin d → O)
    (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1) (f : Fin d → O) :
    ∃ (t : Fin d → O) (l : Fin g → O), t ∈ Submodule.span O (Set.range s) ∧ f = t + Bᵀ *ᵥ l := by
  obtain ⟨-, A', B', -, -, h3⟩ := h
  choose k hk using hT
  set t : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with ht
  have h0 : Aᵀ *ᵥ (f - t) = 0 := by
    rw [Matrix.mulVec_sub, ht, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    rw [sub_eq_zero]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (A * A' + B' * B)ᵀ *ᵥ (f - t) = f - t := by rw [h3]; simp
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add] at h1
  refine ⟨t, B'ᵀ *ᵥ (f - t), ?_, by rw [h1]; abel⟩
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)

private lemma idem_fix {O E : Type} [CommRing O] {g m : ℕ} (ρ : E → Matrix (Fin g) (Fin g) O)
    (ε : Fin m → Matrix (Fin g) (Fin g) O) (sg : Fin m → E → O)
    (horth : ∀ i j, ε i * ε j = if i = j then ε i else 0) (hsum : ∑ i, ε i = 1)
    (heig : ∀ a i, ρ a * ε i = sg i a • ε i) (i : Fin m)
    (hd : ∀ j, i ≠ j → ∃ a, IsUnit (sg i a - sg j a)) (y : Fin g → O)
    (hy : ∀ a, ρ a *ᵥ y = sg i a • y) : ε i *ᵥ y = y := by
  have hl : ∀ a j, ε j * ρ a = sg j a • ε j := by
    intro a j
    have : ρ a = ∑ k, sg k a • ε k := by
      rw [← Matrix.mul_one (ρ a), ← hsum, Matrix.mul_sum]
      simp only [heig]
    rw [this, Matrix.mul_sum]
    simp only [Matrix.mul_smul, horth]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · simp
  have hz : ∀ j, i ≠ j → ε j *ᵥ y = 0 := by
    intro j hj
    obtain ⟨a, ha⟩ := hd j hj
    have h1 : ε j *ᵥ (ρ a *ᵥ y) = sg j a • (ε j *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec]
    rw [hy, Matrix.mulVec_smul] at h1
    have h2 : (sg i a - sg j a) • (ε j *ᵥ y) = 0 := by rw [sub_smul, h1, sub_self]
    exact (ha.smul_eq_zero).1 h2
  have h3 : (∑ j, ε j) *ᵥ y = y := by rw [hsum]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h3
  · exact h3
  · intro b _ hb
    exact hz b hb.symm
  · simp

theorem cokE_surj_res_quot : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (i : Fin U.m) (τ : OE →+* O), (∀ x, U.sg i x = tauExt τ x) → ∀ (n : ℕ) (W : Fin n → Fin d → O), EigB ρG τ W → ∃ f : cokE H.Ht U.εT U.εL i (U.cj i) →ₗ[O] ((Fin n → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k))), Function.Surjective f := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp _ g H d r m A B ρG N s hL U i τ hτ n W hW
  have hsurj := (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d n ρG τ W hW).1
  have hZ : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] (1 : OE)) = algebraMap ℤ_[p] O c • 1 := fun c =>
    (GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g (H.ρL.comp Algebra.TensorProduct.includeLeftRingHom) c
  have hy : ∀ l x, H.ρL x *ᵥ (B *ᵥ W l) = U.sg i x • (B *ᵥ W l) := by
    intro l x
    rw [hτ]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hx, hy, add_smul]
    | tmul c a =>
      have e : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      have e2 : tauExt τ (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * τ a := by
        simp [tauExt, Algebra.ofId_apply]
      rw [e2, e, map_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
        ← hL.eqB, ← Matrix.mulVec_mulVec, hW.1, Matrix.mulVec_smul, mul_smul]
  have hfix : ∀ l, U.εL i *ᵥ (B *ᵥ W l) = B *ᵥ W l := fun l =>
    idem_fix (fun x => H.ρL x) U.εL (fun j x => U.sg j x) U.εL_orth U.εL_sum U.εL_eig i
      (fun j hj => by
        obtain ⟨a, ha⟩ := U.distinct i j hj
        exact ⟨a, hv.isUnit_of_one' ha⟩) _ (hy l)
  have hres : ∀ l : Fin g → O, Pdiv.ChartF.res W (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = Pdiv.ChartF.res W (Bᵀ *ᵥ l) := by
    intro l
    ext k
    change W k ⬝ᵥ (Bᵀ *ᵥ ((U.εL i)ᵀ *ᵥ l)) = W k ⬝ᵥ (Bᵀ *ᵥ l)
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hfix, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  set S : Submodule O (Fin n → O) := Submodule.span O (Set.range fun k => Pdiv.ChartF.res W (s k)) with hS
  have hSm : ∀ t ∈ Submodule.span O (Set.range s), Pdiv.ChartF.res W t ∈ S := by
    intro t ht
    have := Submodule.mem_map_of_mem (f := Pdiv.ChartF.res W) ht
    rwa [Submodule.map_span, ← Set.range_comp] at this
  let F : LinearMap.range (Matrix.mulVecLin (U.εL i)ᵀ) →ₗ[O] ((Fin n → O) ⧸ S) :=
    S.mkQ ∘ₗ Pdiv.ChartF.res W ∘ₗ Matrix.mulVecLin Bᵀ ∘ₗ Submodule.subtype _
  have hF : ∀ x, F x = S.mkQ (Pdiv.ChartF.res W (Bᵀ *ᵥ x.1)) := fun x => rfl
  refine ⟨Submodule.liftQ _ F ?_, ?_⟩
  · rintro x ⟨ν, -, hx⟩
    rw [LinearMap.mem_ker, hF, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply hSm
    have hx' : x.1 = ∑ c, ν c • (fun l => H.Ht l c) := by
      have : H.Ht *ᵥ ν = x.1 := hx
      rw [← this]
      ext l
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hx', Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨k, hk⟩ := hL.fromB c
    rw [Matrix.mulVec_smul, ← hk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · intro z
    obtain ⟨z, rfl⟩ := S.mkQ_surjective z
    obtain ⟨f, rfl⟩ := hsurj z
    obtain ⟨t, l, ht, rfl⟩ := dualNumberPoint_preimage_top_of_reduction A B hL.exact s hL.fromT f
    refine ⟨Submodule.Quotient.mk ⟨(U.εL i)ᵀ *ᵥ l, l, rfl⟩, ?_⟩
    rw [Submodule.liftQ_apply, hF, hres, map_add (f := _), map_add (f := _)]
    have : S.mkQ (Pdiv.ChartF.res W t) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (hSm t ht)
    rw [this, zero_add]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigAdd

private theorem trace_eq (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)]
    (V : Type) [AddCommGroup V] [Module C V] [Module.Finite C V] (ρ : OE →+* Module.End C V) (a : OE) :
    LinearMap.trace C V (ρ a) = ∑ τ : OE →+* C,
      (Module.finrank C ↥(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) : C) * τ a := by
  classical
  obtain ⟨h1, h2⟩ := (GlobalTheory.order_rep_diagonalisable C OE).2 V ρ
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h1 h2
  have hv : ∀ (τ : OE →+* C) (v : V), v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) → ρ a v = τ a • v :=
    fun τ v hv => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  have hf : ∀ τ : OE →+* C, Set.MapsTo (ρ a) ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b))
      ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := fun τ v h => by
    have h' : v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := h
    have := Submodule.smul_mem _ (τ a) h'
    rw [← hv τ v h'] at this
    exact this
  rw [LinearMap.trace_eq_sum_trace_restrict hI hf]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : (ρ a).restrict (hf τ) = τ a • LinearMap.id := by
    ext v
    exact hv τ v.1 v.2
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

private theorem trace_mat (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)] (d : ℕ)
    (ρ : OE →+* Matrix (Fin d) (Fin d) O) (a : OE) :
    algebraMap O C (ρ a).trace = ∑ τ : OE →+* C, (eigDim C ρ τ : C) * τ a := by
  have := trace_eq C OE (Fin d → C)
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin d)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)) a
  refine Eq.trans ?_ this
  change _ = LinearMap.trace C _ (Matrix.toLin' ((ρ a).map (algebraMap O C)))
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]

private theorem coeff_eq (C : Type) [Field C] [CharZero C] (OE : Type) [CommRing OE] [Fintype (OE →+* C)]
    (m n : (OE →+* C) → ℕ) (h : ∀ a, ∑ τ : OE →+* C, (m τ : C) * τ a = ∑ τ : OE →+* C, (n τ : C) * τ a)
    (τ : OE →+* C) : m τ = n τ := by
  have li : LinearIndependent C (fun τ : OE →+* C => (τ : OE → C)) :=
    (linearIndependent_monoidHom OE C).comp (fun τ : OE →+* C => (τ : OE →* C))
      RingHom.coe_monoidHom_injective
  have := Fintype.linearIndependent_iffₛ.1 li (fun τ => (m τ : C)) (fun τ => (n τ : C))
    (by funext a; simpa [Finset.sum_apply] using h a) τ
  exact_mod_cast this

private def trHom {O OE : Type} [CommRing O] [CommRing OE] {d : ℕ} (ρ : OE →+* Matrix (Fin d) (Fin d) O) :
    OE →+* Matrix (Fin d) (Fin d) O where
  toFun a := (ρ a)ᵀ
  map_one' := by simp
  map_mul' a b := by rw [mul_comm a b, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp

theorem eigDim_add_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  intro C _ _ _ O _ _ OE _ _ _ _ _ d r g A B hS ρ ρA ρB hB hA τ
  haveI : Finite (OE →+* C) := (GlobalTheory.order_rep_diagonalisable C OE).1
  letI : Fintype (OE →+* C) := Fintype.ofFinite _
  obtain ⟨-, A', B', h1, h2, h3⟩ := hS
  constructor
  · refine coeff_eq C OE (fun τ => eigDim C ρ τ) (fun τ => eigDim C ρA τ + eigDim C ρB τ) (fun a => ?_) τ
    have ht : (ρ a).trace = (ρA a).trace + (ρB a).trace := by
      have e1 : (ρ a * (A * A')).trace = (ρA a).trace := by
        rw [← Matrix.mul_assoc, hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have e2 : (ρ a * (B' * B)).trace = (ρB a).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, h2,
          Matrix.mul_one]
      rw [← e1, ← e2, ← Matrix.trace_add, ← Matrix.mul_add, h3, Matrix.mul_one]
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← trace_mat, ← trace_mat, ← trace_mat, ht, map_add (f := _)]
  · refine coeff_eq C OE (fun τ => eigDim C (trHom ρ) τ) (fun τ => eigDim C ρ τ) (fun a => ?_) τ
    rw [← trace_mat, ← trace_mat]
    exact congrArg _ (Matrix.trace_transpose _)

end GlobalTheory.EigAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEigenIdem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_eigen_idem {O OE κ : Type} [CommRing O] [CommRing OE] [Fintype κ] [DecidableEq κ]
    {m : ℕ} (t : Fin m → (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (hε : CompleteOrthogonalIdempotents ε)
    (he : ∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = t i a • ε i) (ρ : OE →+* Matrix κ κ O) :
    ∃ e : Fin m → Matrix κ κ O, (∀ i j, e i * e j = if i = j then e i else 0) ∧ ∑ i, e i = 1 ∧
      ∀ a i, ρ a * e i = t i a • e i := by
  let Ψ : O ⊗[ℤ] OE →ₐ[O] Matrix κ κ O :=
    Algebra.TensorProduct.lift (Algebra.ofId O _) ρ.toIntAlgHom
      (fun x y => (Algebra.commutes x _ : Commute (Algebra.ofId O (Matrix κ κ O) x) (ρ.toIntAlgHom y)))
  refine ⟨fun i => Ψ (ε i), fun i j => ?_, ?_, fun a i => ?_⟩
  · rw [← map_mul]
    split_ifs with h
    · subst h; rw [(hε.idem i).eq]
    · rw [hε.ortho h, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, hε.complete, map_one]
  · have h1 : Ψ (1 ⊗ₜ[ℤ] a) = ρ a := by
      refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
      rw [map_one, _root_.one_mul]
      rfl
    rw [← h1, ← map_mul, he, map_smul]

private theorem eigen_ext {p : ℕ} [Fact p.Prime] {O OE κ : Type} [CommRing O] [Algebra ℤ_[p] O] [CommRing OE]
    [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix κ κ O)
    (hρ : ∀ c : ℤ_[p], ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix κ κ O)) (t : OE →+* O)
    (e : Matrix κ κ O) (h : ∀ a, ρ (1 ⊗ₜ[ℤ] a) * e = t a • e) (x : ℤ_[p] ⊗[ℤ] OE) :
    ρ x * e = tauExt t x • e := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), add_mul, add_smul, hx, hy]
  | tmul c a =>
    have h1 : (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] a) := by simp
    have h2 : tauExt t (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * t a := by
      simp [tauExt, Algebra.ofId_apply]
    rw [h2, h1, map_mul, _root_.mul_assoc, h, hρ, smul_mul_assoc, _root_.one_mul, smul_smul]

private theorem frob_ext {p : ℕ} [Fact p.Prime] {O OE : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    [CommRing OE] (hp : ¬IsUnit (p : O)) (s t : OE →+* O)
    (h : ∀ a, s a - t a ^ p ∈ IsLocalRing.maximalIdeal O) (x : ℤ_[p] ⊗[ℤ] OE) :
    tauExt s x - tauExt t x ^ p ∈ IsLocalRing.maximalIdeal O := by
  have hp0 : (p : IsLocalRing.ResidueField O) = 0 := by
    have : IsLocalRing.residue O (p : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hp
    simpa using this
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp0
  have key : ∀ y z : O, y - z ^ p ∈ IsLocalRing.maximalIdeal O ↔
      IsLocalRing.residue O y = frobenius _ p (IsLocalRing.residue O z) := by
    intro y z
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, sub_eq_zero, frobenius_def]
  rw [key]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c a =>
    have h2 : ∀ u : OE →+* O, tauExt u (c ⊗ₜ[ℤ] a : ℤ_[p] ⊗[ℤ] OE) = algebraMap ℤ_[p] O c * u a := by
      intro u
      simp [tauExt, Algebra.ofId_apply]
    have h3 := PadicInt.sub_zmodRepr_mem c
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h3
    obtain ⟨d, hd⟩ := h3
    have h4 : IsLocalRing.residue O (algebraMap ℤ_[p] O c) = (c.zmodRepr : IsLocalRing.ResidueField O) := by
      have : c = d * p + c.zmodRepr := by rw [hd]; ring
      conv_lhs => rw [this]
      simp [hp0]
    rw [h2, h2, map_mul, map_mul, map_mul, (key _ _).1 (h a), h4, map_natCast]

private theorem exists_eigB {O OE : Type} [CommRing O] [IsLocalRing O] [CommRing OE] {g m : ℕ}
    (t : Fin m → (OE →+* O)) (hd : ∀ i j, i ≠ j → ∃ a, IsUnit (t i a - t j a))
    (ρ : OE → Matrix (Fin g) (Fin g) O) (e : Fin m → Matrix (Fin g) (Fin g) O)
    (h1 : ∀ i j, e i * e j = if i = j then e i else 0) (h2 : ∑ i, e i = 1)
    (h3 : ∀ a i, ρ a * e i = t i a • e i) (i : Fin m) :
    ∃ (n : ℕ) (W : Fin n → Fin g → O), EigB ρ (t i) W ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (e i)) ≃ₗ[O] (Fin n → O)) := by
  set N := LinearMap.range (Matrix.mulVecLin (e i)) with hN
  have hid : ∀ w ∈ N, e i *ᵥ w = w := by
    rintro _ ⟨u, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h1, if_pos rfl]
  haveI : Module.Projective O N :=
    Module.Projective.of_split N.subtype (Matrix.mulVecLin (e i)).rangeRestrict
      (by ext1 w; exact Subtype.ext (hid w w.2))
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis O N
  have hcomm : ∀ a j, e j * ρ a = t j a • e j := by
    intro a j
    calc e j * ρ a = e j * (ρ a * ∑ k, e k) := by rw [h2, _root_.mul_one]
      _ = ∑ k, t k a • (e j * e k) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [h3, mul_smul_comm]
      _ = t j a • e j := by
        rw [Finset.sum_eq_single j]
        · rw [h1, if_pos rfl]
        · intro k _ hk
          rw [h1, if_neg (Ne.symm hk), smul_zero]
        · simp
  refine ⟨_, fun k => (b k : Fin g → O), ⟨fun k a => ?_, fun w hw => ?_⟩, ⟨b.equivFun⟩⟩
  · have := hid _ (b k).2
    calc ρ a *ᵥ (b k : Fin g → O) = ρ a *ᵥ (e i *ᵥ (b k : Fin g → O)) := by rw [this]
      _ = t i a • (b k : Fin g → O) := by rw [Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec, this]
  · have hz : ∀ j, j ≠ i → e j *ᵥ w = 0 := by
      intro j hj
      obtain ⟨a, ha⟩ := hd j i hj
      have h5 : (t j a - t i a) • (e j *ᵥ w) = 0 := by
        rw [sub_smul, ← Matrix.smul_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, sub_self]
      exact (ha.smul_eq_zero).1 h5
    have hwN : w ∈ N := by
      refine ⟨w, ?_⟩
      rw [Matrix.mulVecLin_apply]
      calc e i *ᵥ w = ∑ j, e j *ᵥ w := by
            rw [Finset.sum_eq_single i (fun j _ hj => hz j hj) (by simp)]
        _ = w := by rw [← Matrix.sum_mulVec, h2, Matrix.one_mulVec]
    refine ⟨b.equivFun ⟨w, hwN⟩, ?_, fun c hc => ?_⟩
    · have := congrArg Subtype.val (b.sum_equivFun ⟨w, hwN⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum] using this
    · have : b.equivFun.symm c = ⟨w, hwN⟩ := by
        apply Subtype.ext
        rw [Module.Basis.equivFun_symm_apply]
        simpa using hc
      rw [← this, LinearEquiv.apply_symm_apply]

theorem exists_unramData : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) [IsLocalRing O], H.P = 0 → H.PL = 0 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (U : UnramData p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp H) (τ : Fin U.m ≃ (OE →+* O)) (ε : Fin U.m → O ⊗[ℤ] OE), (∀ i x, U.sg i x = tauExt (τ i) x) ∧ (∀ i, U.r i = eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (τ i))) ∧ CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i, τ (U.cj i) = (τ i).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) ∧ ∀ i j, (∀ a, τ j a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O) → U.φ i = j := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ _ cp _ g H _ hP hPL hdisc
  obtain ⟨m, t, ε, φ, hε, he, hd, hφ⟩ := GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius p C v O hv OE hdisc
  let inc : OE →+* ℤ_[p] ⊗[ℤ] OE := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  let ρT : (ℤ_[p] ⊗[ℤ] OE) →+* Matrix (Ix g) (Ix g) O := (algebraMap ℤ_[p] O).mapMatrix.comp H.ρ.toRingHom
  obtain ⟨eT, hT1, hT2, hT3⟩ := exists_eigen_idem (fun i => t i) ε hε he (ρT.comp inc)
  obtain ⟨eL, hL1, hL2, hL3⟩ := exists_eigen_idem (fun i => t i) ε hε he (H.ρL.comp inc)
  have hρT : ∀ c : ℤ_[p], ρT (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Ix g) (Ix g) O) := by
    intro c
    have : H.ρ (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] _ c := H.ρ.commutes c
    change (H.ρ (c ⊗ₜ[ℤ] 1)).map (algebraMap ℤ_[p] O) = _
    rw [this]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  have hρL : ∀ c : ℤ_[p], H.ρL (c ⊗ₜ[ℤ] 1) = algebraMap ℤ_[p] O c • (1 : Matrix (Fin g) (Fin g) O) :=
    fun c => (padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).2 g
      (H.ρL.comp (algebraMap ℤ_[p] (ℤ_[p] ⊗[ℤ] OE))) c
  let st : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  let cj : Fin m → Fin m := fun i => t.symm ((t i).comp st)
  have hcj : Function.Involutive cj := by
    intro i
    apply t.injective
    ext a
    simp [cj, st]
  have hlt : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O → v (algebraMap O C x) < 1 := by
    intro x hx
    refine lt_of_le_of_ne (hv.map_le_one x) fun h => hx ?_
    exact hv.isUnit_of_one' h
  have hone : ∀ (s : OE →+* O) (a : OE), tauExt (p := p) s (1 ⊗ₜ[ℤ] a) = s a := by
    intro s a
    simp [tauExt]
  refine ⟨{ m := m
            sg := fun i => (tauExt (t i)).toRingHom
            εT := eT
            εL := eL
            cj := hcj.toPerm
            φ := φ
            r := fun i => eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp (t i))
            noPad := ⟨hP, hPL⟩
            εT_orth := hT1
            εT_sum := hT2
            εL_orth := hL1
            εL_sum := hL2
            εT_eig := fun a i => eigen_ext ρT hρT (t i) (eT i) (fun b => hT3 b i) a
            εL_eig := fun a i => eigen_ext H.ρL hρL (t i) (eL i) (fun b => hL3 b i) a
            conj := fun i a => ?_
            frob := fun i a => hlt _ (frob_ext hp.out _ _ (hφ i) a)
            distinct := fun i j hij => ?_
            rank := fun i => ?_ }, t, ε, fun _ _ => rfl, fun _ => rfl, hε, he, fun i => ?_, fun i j h => ?_⟩
  · have h1 : t (hcj.toPerm cj i) = (t i).comp st := t.apply_symm_apply _
    change tauExt (t (hcj.toPerm cj i)) a = tauExt (t i) (sigE p OE a)
    rw [h1]
    exact ((embeddings_idempotents_conjugation p C v O hv OE).2.2 (t i) a).1
  · obtain ⟨a, ha⟩ := hd i j hij
    refine ⟨1 ⊗ₜ[ℤ] a, ?_⟩
    change v (algebraMap O C (tauExt (t i) (1 ⊗ₜ[ℤ] a) - tauExt (t j) (1 ⊗ₜ[ℤ] a))) = 1
    rw [hone, hone]
    exact hv.one_of_isUnit ha
  · obtain ⟨n, W, hW, hn⟩ := exists_eigB (fun i => t i) hd (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) eL hL1 hL2 hL3 i
    have := (eigB_res_surjective C v O hv OE g n _ (t i) W hW).2.2
    rw [← this] at hn
    exact hn
  · exact t.apply_symm_apply _
  · by_contra hne
    obtain ⟨a, ha⟩ := hd (φ i) j hne
    have := Ideal.sub_mem _ (hφ i a) (h a)
    rw [sub_sub_sub_cancel_right] at this
    exact this ha

end GlobalTheory.ChF
end

