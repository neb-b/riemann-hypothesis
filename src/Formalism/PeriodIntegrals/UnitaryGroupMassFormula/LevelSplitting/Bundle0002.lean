module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.CompVInvMulVec
section
noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

theorem countable_nf (K : Type) [Field K] [NumberField K] : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

theorem places_countable : PlacesCountable := by
  intro F _ _
  haveI : Countable F := countable_nf F
  haveI : Countable (𝓞 F) := (IsFractionRing.injective (𝓞 F) F).countable
  have hs : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  haveI : Countable (Ideal (𝓞 F)) := hs.countable
  have hinj : Function.Injective (fun P : HeightOneSpectrum (𝓞 F) => P.asIdeal) :=
    fun P Q h => HeightOneSpectrum.ext h
  exact hinj.countable

private theorem mulVec_mem_span_of_mulVec_generators_mem {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G) :
    ∀ x ∈ Submodule.span O G, A.mulVec x ∈ Submodule.span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

theorem stab_iff {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) B) (hCA : ∀ x, C.mulVec (A.mulVec x) = x)
    (hAC : ∀ x, A.mulVec (C.mulVec x) = x) (G : Set (Fin n → B)) :
    (∀ x, x ∈ Submodule.span O G ↔ A.mulVec x ∈ Submodule.span O G) ↔
      ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G ∧ C.mulVec y ∈ Submodule.span O G := by
  constructor
  · intro h y hy
    have hyS : y ∈ Submodule.span O G := Submodule.subset_span hy
    refine ⟨(h y).1 hyS, ?_⟩
    rw [h (C.mulVec y), hAC y]
    exact hyS
  · intro h x
    constructor
    · exact fun hx => mulVec_mem_span_of_mulVec_generators_mem A G (fun y hy => (h y hy).1) x hx
    · intro hx
      have hC := mulVec_mem_span_of_mulVec_generators_mem C G (fun y hy => (h y hy).2) _ hx
      rwa [hCA x] at hC

theorem compV_inv_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.inv_mul, Matrix.one_mulVec]

theorem compV_mulVec_inv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))
    (g : HA (Af F) σ J) (x : Fin n → Fv F v ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
      (Matrix.mulVec ((compV v (incAf σ J g⁻¹) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x) = x := by
  rw [Matrix.mulVec_mulVec, map_inv, map_inv, Units.mul_inv, Matrix.one_mulVec]

theorem measKf_of (h2 : ContPlace) (h3 : LatBorel) : MeasKfAll := by
  intro F E _ _ _ _ _ σ _ M J _ Λ
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := places_countable F
  haveI : Countable E := countable_nf E
  unfold Kf
  rw [Subgroup.coe_iInf]
  refine MeasurableSet.iInter fun v => ?_
  let Mf : HA (Af F) σ J → Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E) := fun g =>
    ((compV v (incAf σ J g) : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
  let G : Set (Fin M → Fv F v ⊗[F] E) := ratV (F := F) (Fv F v) '' Λ
  have hG : G.Countable := (Set.to_countable Λ).image _
  have hset : ((Subgroup.comap ((compV v).comp (incAf σ J)) (Kloc v Λ) : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J)) = ⋂ y ∈ G, ((fun g => (Mf g).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _) ∩
        (fun g => (Mf g⁻¹).mulVec y) ⁻¹' (latLoc (E := E) v Λ : Set _)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    change (∀ x, x ∈ latLoc (E := E) v Λ ↔ (Mf g).mulVec x ∈ latLoc (E := E) v Λ) ↔ _
    exact stab_iff (Mf g) (Mf g⁻¹) (compV_inv_mulVec v g) (compV_mulVec_inv v g) G
  rw [hset]
  refine MeasurableSet.biInter hG fun y _ => ?_
  letI : MeasurableSpace (Fin M → Fv F v ⊗[F] E) := borel _
  haveI : BorelSpace (Fin M → Fv F v ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (fun g => (Mf g).mulVec y) :=
    (h2 F E σ M J v).matrix_mulVec continuous_const
  refine MeasurableSet.inter (hc.measurable (h3 F E M v Λ)) ?_
  have hc' : Continuous (fun g => (Mf g⁻¹).mulVec y) :=
    ((h2 F E σ M J v).comp continuous_inv).matrix_mulVec continuous_const
  exact hc'.measurable (h3 F E M v Λ)

end PI.LevelKSplit.W.Meas
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ContinuousAtPlace
section
noncomputable section

namespace PI.LevelKSplit.W.Cont

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →ₐ[F] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)

theorem phiV_smul (v : HeightOneSpectrum (𝓞 F)) (a : Af F) (x : Af F ⊗[F] E) :
    phiV (E := E) v (a • x) = evalV F v a • phiV v x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

def phiSL (v : HeightOneSpectrum (𝓞 F)) :
    Af F ⊗[F] E →ₛₗ[(evalV F v).toRingHom] Fv F v ⊗[F] E where
  toFun := phiV v
  map_add' := map_add _
  map_smul' := fun a x => phiV_smul v a x

theorem continuous_phiV (v : HeightOneSpectrum (𝓞 F)) : Continuous (phiV (E := E) v) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  have : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
  exact IsModuleTopology.continuous_of_linearMapₛₗ (continuous_evalV v) (phiSL v)

end

theorem continuous_at_place : PI.LevelKSplit.W.Meas.ContPlace := by
  intro F E _ _ _ _ _ σ n J v
  have h1 : Continuous (fun g : HA (Af F) σ J => (incAf σ J g : GL (Fin n) (Af F ⊗[F] E))) :=
    continuous_subtype_val
  have h2 : Continuous (fun g : HA (Af F) σ J =>
      ((incAf σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp h1
  refine (h2.matrix_map (continuous_phiV (E := E) v)).congr ?_
  intro g
  rfl

end PI.LevelKSplit.W.Cont
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOfExistSMeasKf
section
noncomputable section

namespace PI.LevelKSplit.W.Split

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem stab_of (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r) (T : F)
    (hP : P.IsStd σ J T) (ΛX ΛW ΛY : Set (Fin n → E)) (hA : Adapted F E σ n J P ΛX ΛW ΛY)
    (k g : HA (Af F) σ J) (hk : k ∈ Hsub (Af F) σ J P) (hg : g ∈ Kf σ J (ΛX ∪ ΛW ∪ ΛY))
    (hgk : ∀ w ∈ ΛW, lin (Af F) σ J g (ratV (F := F) (Af F) w) -
      lin (Af F) σ J k (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∀ x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY),
      Matrix.mulVec ((compV v (incAf σ J k) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY) := by
  have hgv := (mem_Kf _ g).1 hg v
  have hL : latLoc (E := E) v (ΛX ∪ ΛW ∪ ΛY) = Submodule.span (v.adicCompletionIntegers F)
      (ratV (F := F) (Fv F v) '' ΛX ∪ ratV (F := F) (Fv F v) '' ΛW ∪
        ratV (F := F) (Fv F v) '' ΛY) := by
    rw [latLoc, Set.image_union, Set.image_union]
  have hXfix : ∀ x ∈ ΛX, lin (Af F) σ J k (ratV (F := F) (Af F) x) = ratV (F := F) (Af F) x :=
    fun x hx => lin_fix_span k P.e (H_fix_e P k hk) _ (ratV_mem_span P.e x (hA.1 x hx))
  have hYfix : ∀ x ∈ ΛY, lin (Af F) σ J k (ratV (F := F) (Af F) x) = ratV (F := F) (Af F) x :=
    fun x hx => lin_fix_span k P.f (H_fix_f P k hk) _ (ratV_mem_span P.f x (hA.2.1 x hx))
  intro x hx
  rw [hL] at hx ⊢
  refine Loc.mulVec_span_stable _ _ ?_ x hx
  rintro _ ((⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
  · rw [← phiV_ratV v l, compV_mulVec, hXfix l hl, phiV_ratV]
    exact Submodule.subset_span (Or.inl (Or.inl ⟨l, hl, rfl⟩))
  · have hy : Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (ratV (F := F) (Fv F v) l) ∈
          Submodule.span (v.adicCompletionIntegers F)
            (ratV (F := F) (Fv F v) '' ΛX ∪ ratV (F := F) (Fv F v) '' ΛW ∪
              ratV (F := F) (Fv F v) '' ΛY) := by
      rw [← hL]
      refine (hgv _).1 ?_
      rw [hL]
      exact Submodule.subset_span (Or.inl (Or.inr ⟨l, hl, rfl⟩))
    refine Loc.sep (fun a => ratV (F := F) (Fv F v) (P.e a))
      (fun a => ratV (F := F) (Fv F v) (P.f a)) (fun b => covR (Fv F v) σ J (P.e b))
      (fun b => covR (Fv F v) σ J (P.f b)) ?_ ?_ ?_ _ _ _ ?_ ?_ ?_ _ _ ?_ hy ?_
    · intro a b
      rw [covR_ratV, hP.1 b a, map_zero]
    · intro a b
      rw [covR_ratV, hP.2.2.1 b a]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
    · intro a b
      rw [covR_ratV, hE_swap hJ hinv, hP.2.2.1 a b]
      split_ifs <;> simp
    · rintro _ ⟨x, hx, rfl⟩
      exact ratV_mem_span P.e x (hA.1 x hx)
    · rintro _ ⟨x, hx, rfl⟩
      exact ratV_mem_span P.f x (hA.2.1 x hx)
    · rintro _ ⟨w, hw, rfl⟩ b
      rw [covR_ratV, covR_ratV, (hA.2.2 w hw b).1, (hA.2.2 w hw b).2, map_zero]
      simp
    · intro b
      rw [← phiV_ratV v l, compV_mulVec, ← phiV_cov, ← phiV_cov,
        (H_perp P k hk l (hA.2.2 l hl) b).1, (H_perp P k hk l (hA.2.2 l hl) b).2, map_zero]
      simp
    · rw [← phiV_ratV v l, compV_mulVec, compV_mulVec]
      have : ((fun i => phiV v (lin (Af F) σ J k (ratV (F := F) (Af F) l) i)) -
          fun i => phiV v (lin (Af F) σ J g (ratV (F := F) (Af F) l) i)) =
          fun i => phiV v ((lin (Af F) σ J k (ratV (F := F) (Af F) l) -
            lin (Af F) σ J g (ratV (F := F) (Af F) l)) i) := by
        funext i; simp
      rw [this]
      apply phiV_span
      rw [← neg_sub]
      exact Submodule.neg_mem _ (hgk l hl)
  · rw [← phiV_ratV v l, compV_mulVec, hYfix l hl, phiV_ratV]
    exact Submodule.subset_span (Or.inr ⟨l, hl, rfl⟩)

theorem splitK_level : SplitK F E σ n J := by
  intro hJ hinv r P T hP ΛX ΛW ΛY hA m h hm hh hmh
  have hNm : ∀ m' : HA (Af F) σ J, m' ∈ Nsub (Af F) σ J P → ∀ y, InXperp (Af F) σ J P y →
      lin (Af F) σ J m' y - y ∈ spanR (F := F) (Af F) P.e Set.univ :=
    fun m' hm' y hy => hm'.2 y hy
  have hperp : ∀ w ∈ ΛW, ∀ k : HA (Af F) σ J, k ∈ Hsub (Af F) σ J P →
      InXperp (Af F) σ J P (lin (Af F) σ J k (ratV (F := F) (Af F) w)) := by
    intro w hw k hk a
    rw [hR_ratV_left]
    exact (H_perp P k hk w (hA.2.2 w hw) a).1
  have h1 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h) (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [lin_mul]
    exact hNm m hm _ (hperp w hw h hh)
  have h2 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h)⁻¹ (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h⁻¹ (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [mul_inv_rev, lin_mul, ← map_sub]
    have hp := hperp w hw 1 (Subgroup.one_mem _)
    rw [lin_one] at hp
    have hx := hNm m⁻¹ (Subgroup.inv_mem _ hm) _ hp
    rw [lin_fix_span h⁻¹ P.e (H_fix_e P _ (Subgroup.inv_mem _ hh)) _ (by rwa [spanR_univ] at hx)]
    exact hx
  rw [mem_Kf]
  intro v x
  have s1 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h (m * h) hh hmh h1 v
  have s2 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h⁻¹ (m * h)⁻¹ (Subgroup.inv_mem _ hh)
    (Subgroup.inv_mem _ hmh) h2 v
  constructor
  · exact s1 x
  · intro hx
    have := s2 _ hx
    rwa [map_inv, map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem level_split_all : SplitKAll := by
  intro F E _ _ _ _ _ σ _ M J _
  exact splitK_level

theorem levelSAll_of_existS_measKf (h1 : ExistSAll) (h2 : MeasKfAll) : LevelSAll :=
  levelSAll_of h1 h2 level_split_all

end PI.LevelKSplit.W.Split
end
end

