module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyUnimodular
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.StdHarm

open MvPolynomial

variable {E : Type} [Field E] [NumberField E]

theorem mem_std {n : ℕ} (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, IsIntegral ℤ (v j) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨v j, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.isIntegral_coe

theorem single_mem_std {n : ℕ} (j : Fin n) : (Pi.single j 1 : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro k
  by_cases h : k = j
  · subst h; simpa using isIntegral_one
  · simpa [h] using isIntegral_zero

theorem std_fg (n : ℕ) : (stdLat E n).FG :=
  Submodule.fg_pi fun _ => by
    rw [Submodule.one_eq_span]
    exact Submodule.fg_span_singleton _

variable [IsCMField E]

theorem std_unimod (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Unimod := by
  have hc (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (IsCMField.complexConj E x) :=
    hx.map_of_comp_eq (RingHom.id ℤ) (IsCMField.complexConj E : E →+* E) (RingHom.ext_int _ _)
  intro v
  constructor
  · intro hv w hw
    have h : IsIntegral ℤ (∑ j, IsCMField.complexConj E (v j) * w j) :=
      IsIntegral.sum _ fun j _ => (hc _ ((mem_std v).1 hv j)).mul ((mem_std w).1 hw j)
    exact ⟨⟨_, h⟩, rfl⟩
  · intro h
    refine (mem_std v).2 fun j => ?_
    obtain ⟨y, hy⟩ := h _ (single_mem_std j)
    have h1 : IsCMField.complexConj E (v j) = algebraMap (𝓞 E) E y := by
      rw [hy]
      simp [Pi.single_apply]
    have h2 := hc _ y.isIntegral_coe
    rwa [← h1, IsCMField.complexConj_apply_apply] at h2

variable {H : Host E} {Dw : Datum H} {l : Level H} (c : Coeff l)

theorem symO_std (n : ℕ) : Formalism.L2.Pj.symO (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) =
    (MvPolynomial.map (σ := LtN Dw n) (algebraMap (integralClosure ℤ c.F) c.F)).range := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · exact ⟨C o, by simp⟩
    · refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ ⟨X _, map_X _ _⟩
      have h : IsIntegral ℤ (embF c σ (b j)) :=
        ((mem_std b).1 hb j).map_of_comp_eq (RingHom.id ℤ) (embF c σ) (RingHom.ext_int _ _)
      exact ⟨C ⟨_, h⟩, map_C _ _⟩
  · rintro _ ⟨Q, rfl⟩
    induction Q using MvPolynomial.induction_on with
    | C o => exact Subring.subset_closure (Or.inl ⟨o, by rw [map_C]; rfl⟩)
    | add p q hp hq =>
      rw [(MvPolynomial.map (σ := LtN Dw n) (algebraMap (integralClosure ℤ c.F) c.F)).map_add]
      exact Subring.add_mem _ hp hq
    | mul_X p s hp =>
      rw [map_mul, map_X]
      refine Subring.mul_mem _ hp (Subring.subset_closure (Or.inr ?_))
      obtain ⟨σ, i, j⟩ := s
      refine ⟨σ, i, Pi.single j 1, single_mem_std j, ?_⟩
      rw [letB, Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [hk]
      · simp

theorem harmL_std (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) :
    harmL (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) a = harmA c a n := by
  ext P
  refine and_congr_right fun _ => ?_
  rw [symO_std]
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (AddMonoidAlgebra.coeff Q m).2
  · intro h
    refine mem_range_map_iff_coeffs_subset.2 fun x hx => ?_
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hx
    exact ⟨⟨_, h m⟩, rfl⟩

theorem harmA_mem_span_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), (∀ a : (E →+* ℂ) × ℕ → ℕ, harmL (Dw := Dw) c (⟨stdLat E n⟩ : GenLat E n) a = harmA c a n) ∧ (Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∀ P ∈ harmA (Dw := Dw) c a n, P ∈ Submodule.span c.F {Q : MvPolynomial (LtN Dw n) c.F | Q ∈ harmA c a n ∧ ∀ σ' : c.F →+* ℂ, Real.log (∑ m ∈ Q.support, ‖σ' (Q.coeff m)‖) ≤ 140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a}) := by
  intro E _ _ _ H Dw l c n
  refine ⟨harmL_std c n, fun hn a L hL h1 h2 h3 h4 P hP => ?_⟩
  obtain ⟨S, hS, hspan, -⟩ := _root_.GlobalTheory.Harm.exists_short_harmL_family E H Dw l c n ⟨stdLat E n⟩ (std_unimod n) (std_fg n)
    hn a L hL h1 h2 h3 h4
  refine Submodule.span_mono (fun Q hQ => ?_) (hspan P hP.1)
  exact ⟨harmL_std c n a ▸ (hS Q hQ).1, (hS Q hQ).2⟩

end GlobalTheory.StdHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRawChartBaseChangeJetPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RawChartBC

open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem psTrunc_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {κ : Type} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (f : MvPowerSeries κ S) :
    psTrunc m (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psTrunc m f) := by
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem basis_map {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {σ κ : Type} [Fintype σ] [Fintype κ]
    (U : σ → κ → S) (h : ∀ v : κ → S, ∃! a : σ → S, ∀ j, ∑ ℓ, a ℓ * U ℓ j = v j) (v : κ → S') :
    ∃! a : σ → S', ∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j := by
  classical
  choose N hN hNu using fun k : κ => h (Pi.single k 1)
  let M : Matrix σ κ S := Matrix.of U
  let P : Matrix κ σ S := Matrix.of N
  have h1 : P * M = 1 := by
    ext k j
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (hN k j).trans ?_
    simp [Pi.single_apply, eq_comm]
  have h2 : M * P = 1 := by
    ext ℓ ℓ'
    have e : (fun i => (M * P) ℓ i) = fun i => (1 : Matrix σ σ S) ℓ i := by
      refine (h (U ℓ)).unique (fun j => ?_) (fun j => ?_)
      · have : (M * P * M) ℓ j = M ℓ j := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
        rw [Matrix.mul_apply] at this
        exact this
      · have : ((1 : Matrix σ σ S) * M) ℓ j = M ℓ j := by rw [Matrix.one_mul]
        rw [Matrix.mul_apply] at this
        exact this
    exact congrFun e ℓ'
  have h1' : P.map ψ * M.map ψ = 1 := by rw [← Matrix.map_mul, h1]; simp
  have h2' : M.map ψ * P.map ψ = 1 := by rw [← Matrix.map_mul, h2]; simp
  have key : ∀ a : σ → S', (∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j) ↔ Matrix.vecMul a (M.map ψ) = v := by
    intro a
    rw [funext_iff]
    rfl
  refine ⟨Matrix.vecMul v (P.map ψ), (key _).2 ?_, fun a ha => ?_⟩
  · rw [Matrix.vecMul_vecMul, h1', Matrix.vecMul_one]
  · rw [← (key a).1 ha, Matrix.vecMul_vecMul, h2', Matrix.vecMul_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

section Maps

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap])

def dualPtMap : overAt (spMap ψ ≫ x0) (DualNumber S') ⟶ overAt x0 (DualNumber S) :=
  Over.homMk (spMap (dualMap ψ)) (by
    show spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ rjBC ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetAug_comp_jetBC ψ _ m)

theorem sq_trunc (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetTrunc : Jet S' (Fin 1 × Fin d) (m + 1) →ₐ[S'] Jet S' (Fin 1 × Fin d) m) ≫
        rjBC ψ x0 d (m + 1) 1 =
      rjBC ψ x0 d m 1 ≫ homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (m + 1)) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetTrunc_comp_jetBC ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ rjBC ψ x0 d m n =
      rjBC ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (jetSubstP_comp_jetBC ψ m φ)

theorem sq_tan (d : ℕ) (ℓ : Fin 1 × Fin d) :
    homAt (spMap ψ ≫ x0) (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ rjBC ψ x0 d 1 1 =
      dualPtMap ψ x0 ≫ homAt x0 (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ (0 + 1)) = spMap (dualMap ψ) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  have evalTan (T : Type) [CommRing T] (P : MvPolynomial (Fin 1 × Fin d) T) :
      (jetTan ℓ : Jet T (Fin 1 × Fin d) (0 + 1) →ₐ[T] DualNumber T)
          (Ideal.Quotient.mk (orig T (Fin 1 × Fin d) ^ (0 + 1 + 1)) P) =
        MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber T) else 0) P := rfl
  have hcomp :
      (jetTan ℓ : Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S').toRingHom.comp
          (jetBC ψ (Fin 1 × Fin d) (0 + 1)) =
        (dualMap ψ).comp (jetTan ℓ : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S).toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, evalTan,
        MvPolynomial.aeval_C, MvPolynomial.map_C]
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, jetBC_mk, evalTan,
        MvPolynomial.aeval_X, MvPolynomial.map_X]
      split_ifs <;> ext <;> simp [dualMap]
  exact congrArg spMap hcomp

theorem jetMap_congr_fun {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        rjBC ψ x0 d m 1 =
      rjBC ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  have e := jetMap_comp_jetBC ψ m
    (fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr_fun (show (fun p : Fin 1 × Fin d =>
      MvPolynomial.map ψ (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => MvPolynomial.X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

theorem list_prod_comp {T T' : Over Xo.X} (f : T' ⟶ T) (L : List (T ⟶ Xo.univ.t.G)) :
    (L.map (f ≫ ·)).prod = f ≫ L.prod := by
  induction L with
  | nil => simp [Hom.one_def]
  | cons a L ih => simp only [List.map_cons, List.prod_cons, ih, Hom.mul_def, comp_lift_assoc]

theorem isCombAt_map {k : ℕ} {v : Fin k → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin k → S}
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x0 v cf w) :
    IsCombAt (spMap ψ ≫ x0) (fun i => spMap (dualMap ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMap ψ) ≫ w) := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun i => dualPtMap ψ x0 ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMap ψ) ≫ (u i).left = _
    rw [hu i, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap, Category.assoc]
  · have e : List.ofFn (fun i => dualPtMap ψ x0 ≫ u i) = (List.ofFn u).map (dualPtMap ψ x0 ≫ ·) := by
      rw [List.map_ofFn]
      rfl
    rw [e, list_prod_comp, Over.comp_left, hp]
    rfl

end Maps

theorem rIsChart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ Xo.X) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (x : ∀ m, rjO x0 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, rjO (spMap ψ ≫ x0) d m 1 ⟶ Xo.univ.t.G), (∀ m, x' m = rjBC ψ x0 d m 1 ≫ x m) → ∀ (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (uvec : Lt1 Dw → Fin d → S), RIsChart x0 u d F act uvec x → RIsChart (spMap ψ ≫ x0) (fun τ i => spMap (dualMap ψ) ≫ u τ i) d (fun i => MvPowerSeries.map ψ (F i)) (fun a i => MvPowerSeries.map ψ (act a i)) (fun ℓ j => ψ (uvec ℓ j)) x' := by
  intro E _ _ _ H Dw l Xo S S' _ _ ψ x0 d F act x x' hx' u uvec hX
  obtain rfl : x' = fun m => rjBC ψ x0 d m 1 ≫ x m := funext hx'
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun m a => ?_, fun ℓ => ?_, basis_map ψ uvec hX.basis⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, hX.zero m]
    simp [Hom.one_def]
  · rw [← Category.assoc, sq_trunc, Category.assoc, hX.trunc m]
  · simp only [psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, hX.law m]
    simp only [rjpt, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), ← Category.assoc (homAt _ _) (rjBC _ _ _ _ _), sq_copy,
      sq_copy, Category.assoc, Category.assoc]
  · simp only [psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, hX.act m a]
  · have hv : (fun j : Fin d => (homAt (spMap ψ ≫ x0) (jetTan ((0 : Fin 1), j) :
        Jet S' (Fin 1 × Fin d) (0 + 1) →ₐ[S'] DualNumber S') ≫ (rjBC ψ x0 d 1 1 ≫ x 1)).left) =
        fun j => spMap (dualMap ψ) ≫ (homAt x0 (jetTan ((0 : Fin 1), j) :
          Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
      funext j
      rw [← Category.assoc, sq_tan, Category.assoc]
      rfl
    have := isCombAt_map ψ x0 (hX.tan ℓ)
    rw [← hv] at this
    exact this

end GlobalTheory.RawChartBC
end
end

