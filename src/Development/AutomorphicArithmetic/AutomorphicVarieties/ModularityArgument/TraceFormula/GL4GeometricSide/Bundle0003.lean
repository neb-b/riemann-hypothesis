module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlChar
section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

open NumberField Finset

private theorem map_epow {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) :
    ∀ a b u, j (PositivityTheory.RgBcC.RealD.epow M m a b u) = Formalism.REAL.epow N m a b (j u) := by
  induction m with
  | zero =>
    intro a b u
    by_cases hab : a = b <;> simp [PositivityTheory.RgBcC.RealD.epow, Formalism.REAL.epow, hab]
  | succ m ih =>
    intro a b u
    rw [PositivityTheory.RgBcC.Bridge.epow_succ']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PositivityTheory.RgBcC.RealD.epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h, ih]

private theorem map_gelA {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) (u : U) :
    j (gelA M m u) = Formalism.REAL.etr N m (j u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gelA, Formalism.REAL.etr, LinearMap.sum_apply, map_sum, map_epow j M N h m]

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlChar :
    RlChar := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w lam hch
  have hin : Function.Injective ((π.V.subtype).comp D.i) :=
    Subtype.val_injective.comp D.inj
  have h1 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.1
  have h2 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.2
  constructor
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (D.E1 w) (PositivityTheory.RgBcC.Bridge.eopW w true)
      (fun a b u => D.hE1 w a b u) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h1 _ (D.i x).2 m
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (barF (D.E2 w)) (PositivityTheory.RgBcC.Bridge.eopW w false)
      (fun a b u => by
        have := D.hE2 w b a u
        simp only [barF, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, Submodule.subtype_apply,
          Submodule.coe_neg, this, neg_neg]) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h2 _ (D.i x).2 m
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlComm
section
noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting

section Sum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem exists_sum (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) {S : Set G} (hS : IsCompact S) :
    ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ), ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) →
      (∀ g, g ∉ S → F g = 0) → ∫ g, F g ∂μ = ∑ x ∈ T, c x * F (r x) :=
  _root_.UpperTheory.Reformulated.B.Qg3.exists_sum μ K hKo hKc hS

end Sum

section Ops

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem atW_val (w v : InfinitePlace E) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    atW w X a b v = (if v = w then X else 1) a b := by
  simp only [atW]
  split_ifs <;> rfl

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_mul (w w' v : InfinitePlace E) (X Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' Y)) a b v =
      ((if v = w then X else 1) * (if v = w' then Y else 1)) a b := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, atW_val]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem of_atW_inv (w : InfinitePlace E) {X Y : Matrix (Fin n) (Fin n) ℂ} (h : X * Y = 1) :
    (Matrix.of (atW w X) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w Y) = 1 := by
  ext a b v
  rw [of_atW_mul]
  by_cases hv : v = w
  · simp only [if_pos hv, h]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  · simp only [if_neg hv, mul_one]
    show _ = (1 : Matrix (Fin n) (Fin n) (Cinf E)) a b v
    simp only [Matrix.one_apply]
    split_ifs <;> rfl

private def yAt (w : InfinitePlace E) (k : Un n) : GL (Fin n) (Cinf E) where
  val := Matrix.of (atW w k.1)
  inv := Matrix.of (atW w (star k.1))
  val_inv := of_atW_inv w (Unitary.mul_star_self_of_mem k.2)
  inv_val := of_atW_inv w (Unitary.star_mul_self_of_mem k.2)

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem yAt_comm {w w' : InfinitePlace E} (h : w ≠ w') (k k' : Un n) : yAt w k * yAt w' k' = yAt w' k' * yAt w k := by
  apply Units.ext
  ext a b v
  show ((Matrix.of (atW w k.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w' k'.1)) a b v =
    ((Matrix.of (atW w' k'.1) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (atW w k.1)) a b v
  rw [of_atW_mul, of_atW_mul]
  by_cases h1 : v = w
  · have h2 : v ≠ w' := h1 ▸ h
    simp [h1, h]
  · simp [h1]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
private theorem coord_atW {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (X : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n) : coord τ (atW w X a b) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [PositivityTheory.Rg.Cz.J.coord_eq, atW_val, if_neg h, Matrix.one_apply]
  split_ifs <;> simp

private theorem commute_rt_Eop {τ : E →+* ℂ} {w : InfinitePlace E} (h : InfinitePlace.mk τ ≠ w) (k : Un n) (a b : Fin n) :
    Commute (Eop τ a b) (rt E n (infGL E n (yAt w k))) := by
  have e := GlobalTheory.CapAdInv.rt_Eop (yAt w k) τ a b
  have c1 : ∀ p q, coord τ ((yAt w k).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q := coord_atW h k.1
  have c2 : ∀ p q, coord τ (((yAt w k)⁻¹ : GL (Fin n) (Cinf E)).val p q) = (1 : Matrix (Fin n) (Fin n) ℂ) p q :=
    coord_atW h (star k.1)
  simp only [c1, c2, Matrix.one_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  exact e.symm

private theorem commute_Eop_fin (τ : E →+* ℂ) (a b : Fin n) (g : GL (Fin n) (Af E)) :
    Commute (Eop τ a b) (finRep E n g) := by
  have hl : ∀ x, Commute (lieS E n a b x) (finRep E n g) := fun x => by
    rw [lieS_apply]
    exact lie_rt_fin _ g
  have e : Eop τ a b = (1 / 2 : ℂ) • (lieS E n a b (atEmb τ 1) - Complex.I • lieS E n a b (atEmb τ Complex.I)) := by
    rw [lieS_atEmb_one, lieS_atEmb_I, smul_smul, Complex.I_mul_I]
    module
  rw [e]
  exact ((hl _).sub_left ((hl _).smul_left _)).smul_left _

private theorem commute_rt_fin (y : GL (Fin n) (Cinf E)) (g : GL (Fin n) (Af E)) :
    Commute (rt E n (infGL E n y)) (finRep E n g) := by
  show rt E n (infGL E n y) * rt E n (finGL E n g) = rt E n (finGL E n g) * rt E n (infGL E n y)
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem exists_op [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))]
    (μf : Measure (GL (Fin n) (Af E))) [μf.IsHaarMeasure] (K : Subgroup (GL (Fin n) (Af E)))
    (hKo : IsOpen (K : Set (GL (Fin n) (Af E)))) (hKc : IsCompact (K : Set (GL (Fin n) (Af E))))
    {h : GL (Fin n) (Af E) → ℂ} (hh : IsHeckeF K h) :
    ∃ A : Module.End ℂ (Sm E n), (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧
      ∀ ψ : Sm E n, (∀ k ∈ K, finRep E n k ψ = ψ) → heckeOp μf h ψ.1 = (A ψ).1 := by
  obtain ⟨T, r, c, H⟩ := exists_sum μf K hKo hKc hh.1
  refine ⟨∑ x ∈ T, (c x * h (r x)) • finRep E n (r x), fun B hB => ?_, fun ψ hψ => ?_⟩
  · exact Commute.sum_left _ _ _ fun x _ => ((hB _).symm).smul_left _
  · funext x
    have e := H (fun g => h g * ψ.1 (x * finGL E n g)) (fun g k hk => ?_) (fun g hg => ?_)
    · refine e.trans ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc]
      rfl
    · have e1 : h (g * k) = h g := by simpa using hh.2 1 K.one_mem k hk g
      have e2 : ψ.1 (x * finGL E n g * finGL E n k) = ψ.1 (x * finGL E n g) :=
        congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hψ k hk)
      simp only [e1, map_mul, ← mul_assoc, e2]
    · simp [image_eq_zero_of_notMem_tsupport hg]

end Ops

theorem rlComm : RlComm := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D
  let ι : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hinj : Function.Injective ι := π.V.injective_subtype.comp D.inj
  have lift : ∀ (A B : Module.End ℂ D.U) (A' B' : Module.End ℂ (Sm E n)), (∀ u, ι (A u) = A' (ι u)) →
      (∀ u, ι (B u) = B' (ι u)) → Commute A' B' → Commute A B := fun A B A' B' hA hB hc =>
    LinearMap.ext fun u => hinj <| by
      have := LinearMap.congr_fun hc.eq (ι u)
      simp only [Module.End.mul_apply] at this ⊢
      rw [hA, hB, hB, hA, this]
  have h1 : ∀ w a b u, ι (D.E1 w a b u) = Eop w.embedding a b (ι u) := fun w a b u => D.hE1 w a b u
  have h2 : ∀ w a b u, ι (D.E2 w a b u) = (-Eop (ComplexEmbedding.conjugate w.embedding) b a) (ι u) :=
    fun w a b u => D.hE2 w a b u
  have h3 : ∀ w k u, ι (D.σ w k u) = rt E n (infGL E n (yAt w k)) (ι u) := fun w k u =>
    Subtype.ext <| funext fun g => (D.hσ w k u g).trans (chart_val _ g (yAt w k))
  have h4 : ∀ h : {h : GL (Fin n) (Af E) → ℂ // IsHeckeF K h}, ∃ A : Module.End ℂ (Sm E n),
      (∀ B : Module.End ℂ (Sm E n), (∀ g, Commute B (finRep E n g)) → Commute A B) ∧ ∀ u, ι (D.R h u) = A (ι u) := fun h => by
    obtain ⟨A, hA, hA'⟩ := exists_op μf K hKo hKc h.2
    exact ⟨A, hA, fun u => Subtype.ext ((D.hR h u).trans (hA' _ ((D.rng (D.i u)).1 ⟨u, rfl⟩)))⟩
  have mk1 : ∀ w : InfinitePlace E, InfinitePlace.mk w.embedding = w := InfinitePlace.mk_embedding
  have mk2 : ∀ w : InfinitePlace E, InfinitePlace.mk (ComplexEmbedding.conjugate w.embedding) = w := fun w => by
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have ne : ∀ {τ τ' : E →+* ℂ}, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → τ ≠ τ' := fun h e => h (e ▸ rfl)
  refine ⟨fun i j hij a b => ⟨fun c d => ⟨?_, ?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun i j hij k k' => ?_, fun h i => ⟨fun a b => ⟨?_, ?_⟩, fun k => ?_⟩⟩
  · exact lift _ _ _ _ (h1 i a b) (h1 j c d) (Eop_comm (ne (by rwa [mk1, mk1])) a b c d)
  · exact lift _ _ _ _ (h1 i a b) (h2 j c d) (Commute.neg_right (Eop_comm (ne (by rwa [mk1, mk2])) a b d c))
  · exact lift _ _ _ _ (h2 i a b) (h2 j c d) (Commute.neg_left (Commute.neg_right (Eop_comm (ne (by rwa [mk2, mk2])) b a d c)))
  · exact lift _ _ _ _ (h1 i a b) (h3 j k) (commute_rt_Eop (by rwa [mk1]) k a b)
  · exact lift _ _ _ _ (h2 i a b) (h3 j k) (Commute.neg_left (commute_rt_Eop (by rwa [mk2]) k b a))
  · refine (lift _ _ _ _ (h3 i k) (h3 j k') ?_).eq
    show rt E n (infGL E n (yAt i k)) * rt E n (infGL E n (yAt j k')) = rt E n (infGL E n (yAt j k')) * rt E n (infGL E n (yAt i k))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, yAt_comm hij]
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h1 i a b) (hA _ fun g => commute_Eop_fin _ a b g)
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h2 i a b) (hA _ fun g => Commute.neg_left (commute_Eop_fin _ b a g))
  · obtain ⟨A, hA, hA'⟩ := h4 h
    exact lift _ _ _ _ hA' (h3 i k) (hA _ fun g => commute_rt_fin _ g)

end UpperTheory.V.Z.GSp4Splitting
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlPair
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL GlobalTheory.UnitaryBC
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

private theorem adj_of_skew {M : Type} [AddCommGroup M] [Module ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (A B : Module.End ℂ M)
    (h : ∀ (z : ℂ) (φ ψ : M), H ((z • A + star z • B) φ) ψ + H φ ((z • A + star z • B) ψ) = 0)
    (φ ψ : M) : H (A φ) ψ = - H φ (B ψ) := by
  have h1 := h 1 φ ψ
  have hI := h Complex.I φ ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, one_smul, star_one,
    Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul,
    Complex.conj_conj, LinearMap.neg_apply] at h1 hI
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI +
    ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq

private theorem lie_single {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (z : ℂ) :
    lieOp π (fun i j => atEmb τ (Matrix.single a b z i j)) =
      z • cx τ (lieOp π) a b + star z • cx (PositivityTheory.Rg.Cz.barE E τ) (lieOp π) a b := by
  rw [PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Matrix.single_apply, hj.symm]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, hi.symm]
  · simp

private theorem cx_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (ψ : π.V) : (cx τ (lieOp π) a b ψ).1 = Eop τ a b ψ.1 := by
  rw [← GlobalTheory.WigCap.res_Eop]
  rfl

private theorem emb_ne {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc : w.IsComplex := IsTotallyComplex.isComplex w
  exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)

private theorem gl_pull {U M : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : U →ₗ[ℂ] M) (hJ : Function.Injective J) (e : Fin n → Fin n → Module.End ℂ U)
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) (h : ∀ a b u, J (e a b u) = F a b (J u)) : GlRel e := by
  intro a b c d
  refine LinearMap.ext fun u => hJ ?_
  have key := LinearMap.congr_fun (hF a b c d) (J u)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, map_sub, h, h, h, h, key]
  split_ifs <;> simp [h]

private theorem gl_neg_swap {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) : GlRel (fun a b => -F b a) := by
  intro a b c d
  have key := hF b a d c
  simp only [neg_mul_neg]
  rw [key]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp; abel
  · have h2' : ¬ a = d := fun h => h2 h.symm
    subst h1
    simp [h2, h2']
  · subst h2
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1']
  · have h2' : ¬ a = d := fun h => h2 h.symm
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1', h2, h2']

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlPair :
    RlPair := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := emb_ne w
  let A : Fin n → Fin n → Module.End ℂ π.V := cx w.embedding (lieOp π)
  let B : Fin n → Fin n → Module.End ℂ π.V := cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)
  have v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1 := fun a b u => D.hE1 w a b u
  have v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1 :=
    fun a b u => D.hE2 w a b u
  have iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u) := fun a b u =>
    Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)
  have iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u) := fun a b u =>
    Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))
  have adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ) := fun a b =>
    adj_of_skew D.H _ _ fun z φ ψ => by
      rw [← lie_single]
      exact D.pet.2.2.1 _ φ ψ
  have adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ) := fun a b φ ψ => by
    have h := congrArg (starRingEnd ℂ) (adjA a b ψ φ)
    rw [map_neg, D.pet.1, D.pet.1] at h
    rw [h, neg_neg]
  have hJ : Function.Injective (π.V.subtype ∘ₗ D.i) := π.V.injective_subtype.comp D.inj
  refine { gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }
  · exact gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1
  · exact gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2
  · intro a b c d
    refine LinearMap.ext fun u => D.inj (Subtype.ext ?_)
    change (D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1
    rw [v1, v2, v2, v1, map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)
  · intro a b x y
    simp only [kF, LinearMap.add_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_add (f := _), iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]
    ring
  · intro a b x y
    simp only [pF, LinearMap.sub_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]
    ring
end

