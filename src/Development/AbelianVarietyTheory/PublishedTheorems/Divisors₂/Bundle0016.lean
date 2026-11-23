module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def ArFormExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ Φ, IsArFun L D Φ

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
section
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT bc)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure IsAdapted (X Y : Matrix (Fin n) (Fin r) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) : Prop where
  lat : Submodule.IsFullLattice E L
  dual : ∀ v, IsSelfDualAt σ J L v
  split : ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L
  maj : IsMajorantFrame σ J a
  cartan : ∀ w : InfinitePlace F, ∃ c : Fin r → w.Completion ⊗[F] E,
    cT (sigR _ σ) (bc (compInf F E w) a⁻¹).1 * (bc (compInf F E w) a⁻¹).1 * X.map (inclR (F := F) w.Completion) =
      (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) * diagonal c

def IsModerateForm (μ : (GAd σ J → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ (S : List (List (ℝ → GAd σ J))) (C : ℝ), (∀ l ∈ S, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSmoothModerate σ J f →
      (∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ B : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ B * (height σ J g : ℝ) ^ N) →
      (∀ l ∈ S, ∀ g, ‖l.foldr lineDer f g‖ ≤ (height σ J g : ℝ) ^ N) → ‖μ f‖ ≤ C

end GlobalTheory.EisLine

namespace GlobalTheory.Published


open GlobalTheory.EisLine in
def EisensteinIsotropicLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x y : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → y = Y.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
        (∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
          ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
            HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)) ∧
        (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
          ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
            IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
            ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
              Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
              ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
                c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
        MeromorphicOn c Set.univ ∧
        (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
        ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.Whittaker

section Bridge

variable {k : Type} [Field k] {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem superDiag_eq_sum_pairs (g : GL (Fin N) k) :
    superDiag g = ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1, g.val p.1 p.2 := by
  simp only [superDiag, Finset.sum_filter, Fintype.sum_prod_type]

theorem val_whitChar (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    ((GlobalTheory.LocGL.whitChar ψ N u : ℂˣ) : ℂ) = ψ (superDiag u.1) := by
  rw [superDiag_eq_sum_pairs]; rfl

theorem isGeneric_iff_isGenericFor (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    IsGeneric ψ π ↔ GlobalTheory.LocGL.IsGenericFor ψ π := by
  constructor
  · rintro ⟨l, hl, h⟩
    refine Submodule.Quotient.nontrivial_iff.2 fun htop => hl (LinearMap.ker_eq_top.1 (eq_top_iff.2 (htop ▸ ?_)))
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar, h u.1 u.2 v, sub_self]
  · intro h
    have h1 := Submodule.Quotient.nontrivial_iff.1 h
    obtain ⟨l, hl, hk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h1)
    refine ⟨l, hl, fun u hu v => ?_⟩
    have h2 := hk (Submodule.subset_span ⟨⟨u, hu⟩, v, rfl⟩)
    simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, val_whitChar] at h2
    exact sub_eq_zero.1 h2

theorem IsGeneric.of_surjective {ψ : AddChar k Circle} {π : Representation ℂ (GL (Fin N) k) V}
    {σ : Representation ℂ (GL (Fin N) k) W} (f : π.IntertwiningMap σ) (hf : Function.Surjective f) (h : IsGeneric ψ σ) :
    IsGeneric ψ π := by
  obtain ⟨l, hl, h⟩ := h
  refine ⟨l ∘ₗ f.toLinearMap, fun e => hl (LinearMap.ext fun w => ?_), fun u hu v => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    exact LinearMap.congr_fun e v
  · exact (congrArg l (f.isIntertwining _ _ u v)).trans (h u hu _)

end Bridge

section Exact

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem isSmoothChar_whitChar {ψ : AddChar k Circle} (hψ : Continuous ψ) : IsSmoothChar (GlobalTheory.LocGL.whitChar ψ N) := by
  obtain ⟨r, hr⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  have hc : Continuous fun u : unipB k (Fin N) => superDiag u.1 :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have h0 : superDiag ((1 : unipB k (Fin N)) : GL (Fin N) k) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj =>
      Matrix.one_apply_ne fun e => by have := (Finset.mem_filter.1 hj).2; rw [e] at this; omega
  refine (GlobalTheory.LocGL.whitChar ψ N).ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset
    (((GlobalTheory.SplitWeil.isOpen_cball r).preimage hc).mem_nhds ?_) fun u hu => Units.ext ?_)
  · rw [Set.mem_preimage, h0]
    simp [GlobalTheory.SplitWeil.cball]
  · rw [val_whitChar, hr _ hu]; rfl


end Exact

end GlobalTheory.Whittaker

namespace GlobalTheory.Published

open GlobalTheory.Whittaker

def CuspidalGeneric : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) Circle), Continuous ψ → ψ ≠ 1 →
    GlobalTheory.Whittaker.IsGeneric ψ (π.locRep w)


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in
theorem cuspidalGeneric_holds : CuspidalGeneric := by
  intro E _ _ _ a _ P w ψ' hc' h1'
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CuspGeneric.exists_stdPsi E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => _root_.GlobalTheory.CuspGeneric.good_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  have := Submodule.nontrivial_iff_ne_bot.2 P.ne_bot
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : P.V)
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := _root_.GlobalTheory.CuspGeneric.exists_split_loc E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hgen : GlobalTheory.Whittaker.IsGeneric (locPsi hψ w) (P.locRep w) := by
    refine ⟨l, fun e => hne (by rw [e]; rfl), fun u hu v => ?_⟩
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.CuspRep.locTri_adelic E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  exact (isGeneric_iff_isGenericFor _ _).2 ((GlobalTheory.LocGL.isGenericFor_iff_of_continuous hcont hne1 hc' h1' _).1
    ((isGeneric_iff_isGenericFor _ _).1 hgen))

def GenericityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (N c : ℕ) (m : Fin c → ℕ) (e : (Σ a, Fin (m a)) ≃ Fin N) (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Levi k fun a => Fin (m a)) W), IsSmooth ρ → GlobalTheory.Whittaker.IsGeneric ψ (parInd e ρ) →
      ∃ l : Module.Dual ℂ W, l ≠ 0 ∧ ∀ u : Levi k fun a => Fin (m a), (∀ a, u a ∈ unipB k (Fin (m a))) →
        ∀ v, l (ρ u v) = (∏ a, (ψ (superDiag (u a)) : ℂ)) * l v

namespace GenericityGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GenericityGL

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LbH0EqChiStructureModuleOfKrullDimZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefNumericsModel

section General
variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

end General

section Space
open ProjSpace
variable (k : Type) [Field k]

theorem selfIntersection_O1 (N : ℕ) : topSelfIntersection k (O1 k N) N = 1 := by
  have hc : ∀ j : ℕ, chi k (twistZ (structureModule (PSpace k N)) (O1 k N) (-(j : ℤ))) =
      Ring.choose (-(j : ℤ) + N) N := fun j => ProjCoh.chi_sheafO k N _
  rw [topSelf_def, interNum_const_eq_sum k _ (O1_isLB k N) N, Finset.sum_eq_single 0]
  · rw [hc]
    simp [Ring.choose_natCast]
  · intro j hj hj0
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hn : -(j : ℤ) + N = ((N - j : ℕ) : ℤ) := by
      rw [Nat.cast_sub hjN]; ring
    rw [hc, hn, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show N - j < N by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) h

end Space

end GlobalTheory.NefNumericsModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RallisTowerUnitary
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def RallisTowerUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E),
    (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 →
  ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW m →
  ∀ f : UA σ JW → ℂ,
    (∃ (c₀ : E) (K : Subgroup (GAd σ (c₀ • JW.map σ))) (φ : GAd σ (c₀ • JW.map σ) → ℂ), IsHermND σ (c₀ • JW.map σ) ∧
      GlobalTheory.UAut.IsMaxCpt σ (c₀ • JW.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • JW.map σ) K φ ∧
      GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • JW.map σ) φ ∧
      ∀ (h : UA σ JW) (h' : GAd σ (c₀ • JW.map σ)), h.1 = h'.1 → φ h' = f h) →
    (∀ (n₁ k : ℕ) (J₁ : Matrix (Fin n₁) (Fin n₁) E), 1 ≤ k → n₁ + 2 * k = n → (∀ i j, σ (J₁ j i) = J₁ i j) → J₁.det ≠ 0 →
      ∀ co₁ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n₁ × Fin m),
        (∀ x : Matrix (Fin n₁) (Fin m) E, ∃ y z : Fin n₁ × Fin m → F,
          co₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om₁ : UA σ J₁ × UA σ JW →* Module.End ℂ ((Fin n₁ × Fin m → AF F) → ℂ),
        IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co₁ χX χW om₁ →
      ∀ Φ₁ ∈ schA F (Fin n₁ × Fin m), ∀ (g : UA σ J₁) (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JW) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om₁ (g, h) Φ₁)) ∂μ = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
    IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om →
  ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
    IsFundamentalDomain (ratU σ JW) 𝓕 μ →
  ∀ c : E, IsHermND σ (c • JX.map σ) → ∀ th : GAd σ (c • JX.map σ) → ℂ,
    (∀ (g : UA σ JX) (g' : GAd σ (c • JX.map σ)), g.1 = g'.1 →
      th g' = ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ) →
    GlobalTheory.SiegelSet.IsCuspidal σ (c • JX.map σ) th

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SerreHolomorphicSections
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.Vanishing

namespace GlobalTheory.Published

def SerreHolomorphicSections : Prop :=
  ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p →
    ∀ (R : AnRead p (RingHom.id ℂ) D) (B : LB Y), B.IsLB →
      Function.Bijective fun s : B.Sec =>
        (⟨secVal p (RingHom.id ℂ) s, R.secVal_mem_holSec s⟩ : R.holSec B)

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {q : Y' ⟶ Sp k'}
  {r : Y' ⟶ Y} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D D' : ℕ} {m : CxPts q τ → CxPts p σ} {B : LB Y}


variable (r m B) in
def pullVal : (B.ι → CxPts p σ → ℂ) →ₗ[ℂ] ((B.pull r).ι → CxPts q τ → ℂ) where
  toFun s J z := s (J PUnit.unit) (m z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullVal_injective (hb : Function.Surjective m) : Function.Injective (pullVal r m B) :=
  fun _ _ h => funext₂ fun i y => by
    obtain ⟨z, rfl⟩ := hb y
    exact congrFun₂ h (fun _ => i) z

theorem mem_ptsIn_pull (hm : ∀ z, (m z).1 = z.1 ≫ r) {J : (B.pull r).ι} {z : CxPts q τ} :
    z ∈ ptsIn q τ ((B.pull r).U J) ↔ m z ∈ ptsIn p σ (B.U (J PUnit.unit)) := by
  rw [← mem_ptsIn_preimage hm, mem_ptsIn, mem_ptsIn]
  exact mem_pull

theorem pullVal_mem_holSec (hm : ∀ z, (m z).1 = z.1 ≫ r) {R : AnRead p σ D} (R' : AnRead q τ D')
    {s : B.ι → CxPts p σ → ℂ} (hs : s ∈ R.holSec B) : pullVal r m B s ∈ R'.holSec (B.pull r) := by
  refine ⟨⟨fun J J' z h h' => ?_, fun J z h => hs.1.2 _ _ (mt (mem_ptsIn_pull hm).2 h)⟩, fun J =>
    ((hs.2 _).comp_map (isOpen_ptsIn _) hm R').mono fun _ hz => (mem_ptsIn_pull hm).1 hz⟩
  rw [gv_linComb (m := fun _ => m z) (fun _ => hm z) h h', Fintype.prod_unique, zpow_one]
  exact hs.1.1 _ _ _ ((mem_ptsIn_pull hm).1 h) ((mem_ptsIn_pull hm).1 h')

theorem cval_pullChart_ofSec {ρ : k →+* k'} (hm : ∀ z, (m z).1 = z.1 ≫ r) (w : r ≫ p = q ≫ spMap ρ)
    (s : B.Sec) : cval τ (pullChart (W := ⊤) (GlobalTheory.chartPullPull B r) w le_top (H0.ofSec p ⊤ s)) =
      pullVal r m B (secVal p σ s) := funext₂ fun J z => by
  by_cases h : z ∈ ptsIn q τ ((B.pull r).U J)
  · rw [cval_pullChart hm _ _ _ h, cval_ofSec]
    rfl
  · exact ((cval_mem _ _).2 _ _ h).trans ((secVal_mem s).2 _ _ (mt (mem_ptsIn_pull hm).2 h)).symm

end BaseChange

theorem SerreHolomorphicSections.bijective_valC (h : SerreHolomorphicSections) {F : Type} [Field F]
    {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ} [SmoothOfRelativeDimension D p] (hp : IsProjOver p)
    (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) : Function.Bijective (R.valC B) := by
  let := σ.toAlgebra
  have H := IsPullback.of_hasPullback p (spMap σ)
  generalize Limits.pullback.fst p (spMap σ) = r at H
  generalize Limits.pullback.snd p (spMap σ) = q at H
  have hq := ProjSpace.isProjOver_of_isPullback_spMap σ H hp
  have hs : SmoothOfRelativeDimension D q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange D
    MorphismProperty.of_isPullback H ‹SmoothOfRelativeDimension D p›
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts q (RingHom.id ℂ) → CxPts p σ, (∀ z, (m z).1 = z.1 ≫ r) ∧
      Function.Surjective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, (bijective_bcMap H _).2⟩
  have hB' := LB.isLB_pull hB r
  have hS := h _ q D hs hq (AnRead.all _ _ D) _ hB'
  have hE := isExtension_pullChart_top (k := F) (E := ℂ) H hB hB' (GlobalTheory.chartPullPull B r) hp hq
  set ι := pullChart (O := ⊤) (W := ⊤) (GlobalTheory.chartPullPull B r) H.w le_top
  let L : SecC p σ B →ₗ[ℂ] H0 q (B.pull r) ⊤ :=
    SecC.lift (ι.toAddMonoidHom.comp (H0.ofSec p ⊤)) fun a s =>
      (congrArg ι (H0.ofSec_smul a s)).trans (map_smulₛₗ ι a _)
  have hL (s) : L (SecC.of p σ s) = ι (H0.ofSec p ⊤ s) := SecC.lift_of _ _ s
  have hc (x) : cval (RingHom.id ℂ) (L x) = pullVal r m B (SecC.val x) := by
    refine LinearMap.eqOn_span' (f := cval (RingHom.id ℂ) ∘ₗ L) (g := pullVal r m B ∘ₗ SecC.val)
      (s := range (SecC.of p σ)) ?_ (SecC.span_range_of.ge Submodule.mem_top)
    rintro _ ⟨s, rfl⟩
    simp only [LinearMap.comp_apply, hL, SecC.val_of]
    exact cval_pullChart_ofSec hm H.w s
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun s => ?_⟩
  · have h₀ : L x = 0 := by
      obtain ⟨t, ht⟩ := H0.bijective_ofSec_top.2 (L x)
      have e := hc x
      rw [← ht, cval_ofSec, show SecC.val x = 0 from congrArg Subtype.val hx, map_zero] at e
      rw [← ht, hS.1 (a₁ := t) (a₂ := 0) (Subtype.ext (e.trans (map_zero _).symm)), map_zero]
    have := finite_top hp hB
    let b := Module.finBasis F (H0 p B ⊤)
    choose v hv using fun i => H0.bijective_ofSec_top.2 (b i)
    have hx' : x ∈ Submodule.span ℂ (range fun i => SecC.of p σ (v i)) := by
      refine (SecC.span_range_of.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨s, rfl⟩
      have e : s = ∑ i, DVR.FlatBC.algX p ⊤ (b.repr (H0.ofSec p ⊤ s) i) • v i :=
        (H0.bijective_ofSec_top (p := p)).1 (by simp only [map_sum, H0.ofSec_smul, hv, b.sum_repr])
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [SecC.of_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hL, hv] at h₀
    simp [Fintype.linearIndependent_iff.1 (hE.indep _ b b.linearIndependent) c h₀]
  · obtain ⟨t, ht⟩ := hS.2 ⟨_, pullVal_mem_holSec hm (AnRead.all _ _ D) s.2⟩
    have hr : H0.ofSec q ⊤ t ∈ LinearMap.range L := by
      refine (hE.span.ge.trans (Submodule.span_le.2 ?_)) Submodule.mem_top
      rintro _ ⟨f, rfl⟩
      obtain ⟨u, rfl⟩ := H0.bijective_ofSec_top.2 f
      exact ⟨_, hL u⟩
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, Subtype.ext (pullVal_injective (r := r) hb ((hc x).symm.trans ?_))⟩
    rw [hx, cval_ofSec]
    exact congrArg Subtype.val ht

end GlobalTheory.Published
end
end

