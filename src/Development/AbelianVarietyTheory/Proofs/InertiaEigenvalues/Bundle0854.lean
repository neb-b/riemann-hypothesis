module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubquotient
section
namespace GlobalTheory.QuotientGenerator

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def gen (ρ : Representation ℂ G V) (x : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g x)
  apply_mem_toSubmodule g v hv := by
    have h : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤ Submodule.span ℂ (Set.range fun g => ρ g x) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    exact h ⟨v, hv, rfl⟩

theorem self_mem_gen (ρ : Representation ℂ G V) (x : V) : x ∈ (gen ρ x).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem eq_top_of_mem (ρ : Representation ℂ G V) (x : V) (M : Subrepresentation (gen ρ x).toRepresentation)
    (hx : (⟨x, self_mem_gen ρ x⟩ : (gen ρ x).toSubmodule) ∈ M.toSubmodule) : M.toSubmodule = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have h : (gen ρ x).toSubmodule ≤ M.toSubmodule.map (gen ρ x).toSubmodule.subtype := by
    change Submodule.span ℂ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, M.apply_mem_toSubmodule g hx, rfl⟩
  obtain ⟨w, hw, rfl⟩ := h hv
  exact hw

theorem exists_maximal (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ M : Subrepresentation ρ, Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M := by
  have key := zorn_le_nonempty₀ {N : Subrepresentation ρ | x ∉ N.toSubmodule} ?_ ⊥ hx
  · obtain ⟨m, -, hm⟩ := key
    exact ⟨m, hm⟩
  intro c hc hch y hy
  have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
  have hd : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨d, hd, h1, h2⟩ := hch.directedOn a ha b hb
    exact ⟨_, ⟨d, hd, rfl⟩, h1, h2⟩
  refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), fun g v hv => ?_⟩, fun h => ?_, fun z hz => ?_⟩
  · rw [Submodule.mem_sSup_of_directed hne hd] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, a.apply_mem_toSubmodule g hv⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := (Submodule.mem_sSup_of_directed hne hd).1 h
    exact hc ha hv
  · exact (le_sSup ⟨z, hz, rfl⟩ : z.toSubmodule ≤ sSup (Subrepresentation.toSubmodule '' c))

noncomputable def quot (ρ : Representation ℂ G V) (M : Subrepresentation ρ) : Representation ℂ G (V ⧸ M.toSubmodule) :=
  ρ.quotient M.toSubmodule fun g _ hv => M.apply_mem_toSubmodule g hv

theorem quot_mk (ρ : Representation ℂ G V) (M : Subrepresentation ρ) (g : G) (v : V) :
    quot ρ M g (M.toSubmodule.mkQ v) = M.toSubmodule.mkQ (ρ g v) := rfl

theorem quot_irreducible (ρ : Representation ℂ G V) (x : V)
    (hcyc : ∀ N : Subrepresentation ρ, x ∈ N.toSubmodule → N.toSubmodule = ⊤) (M : Subrepresentation ρ)
    (hM : Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M) : (quot ρ M).IsIrreducible := by
  have hx0 : M.toSubmodule.mkQ x ≠ 0 := fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h)
  haveI : Nontrivial (Subrepresentation (quot ρ M)) := ⟨⟨⊥, ⊤, fun h => hx0 (by
    have h1 : M.toSubmodule.mkQ x ∈ (⊤ : Subrepresentation (quot ρ M)).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact h1)⟩⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation ρ := ⟨T.toSubmodule.comap M.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  by_cases hx : x ∈ T'.toSubmodule
  · right
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    have : v ∈ T'.toSubmodule := by rw [hcyc T' hx]; trivial
    exact this
  · left
    have hle : M ≤ T' := fun v hv => by
      change M.toSubmodule.mkQ v ∈ T.toSubmodule
      have : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
      rw [this]
      exact zero_mem _
    have hge : T' ≤ M := hM.2 hx hle
    apply Subrepresentation.toSubmodule_injective
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 (hge (show v ∈ T' from hw))

theorem exists_irreducible_subquotient (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V)
    (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      Representation.IsIrreducible τ ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
      ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
        ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y := by
  let x' : (gen ρ x).toSubmodule := ⟨x, self_mem_gen ρ x⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  obtain ⟨M, hM⟩ := exists_maximal (gen ρ x).toRepresentation x' hx'
  refine ⟨_, inferInstance, inferInstance, quot _ M, M.toSubmodule.mkQ x',
    quot_irreducible _ x' (eq_top_of_mem ρ x) M hM,
    ⟨gen ρ x, ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext fun v => (quot_mk _ M g v).symm⟩, M.toSubmodule.mkQ_surjective⟩,
    fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h), fun ι s f c b h => ?_⟩
  have h' : ∑ i ∈ s, c i • (gen ρ x).toRepresentation (f i) x' = b • x' := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h
  have h2 := congrArg M.toSubmodule.mkQ h'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul] at h2
  simpa only [map_smul, quot_mk] using h2

end GlobalTheory.QuotientGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMap
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType GlobalTheory.StepData GlobalTheory.ProdSupport Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_parVec_of_map : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  intro F _ _ _ _ p _ α n _ _ _ _ m _ _ e X _ _ s a θ χ U _ _ ρ φ hp hθ hs hφ hint
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  let Λ : U →ₗ[ℂ] (⨂[ℂ] b, X b) :=
    { toFun := fun w => (φ w).1.1 1
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hΛ : ∀ w, Λ w = (φ w).1.1 1 := fun _ => rfl
  have hΛ0 : Λ ≠ 0 := by
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra! h
      exact hφ (LinearMap.ext h)
    obtain ⟨x, hx⟩ : ∃ x, (φ w).1.1 x ≠ 0 := by
      by_contra! h
      exact hw (Subtype.ext (Subtype.ext (funext h)))
    obtain ⟨q, κ, hκ, rfl⟩ := MultiIrr.exists_parab_mul e x
    obtain ⟨g, hg⟩ := exists_isLift_of_mem_KO hp hκ
    intro h0
    apply hx
    have h1 : (φ w).1.1 κ = 0 := by
      have h2 : Λ (ρ g w) = 0 := by rw [h0]; rfl
      rw [hΛ, ← hint g κ hg w] at h2
      have h3 : (multiProd e s κ (φ w)).1.1 1 = (φ w).1.1 (1 * κ) := rfl
      rwa [h3, one_mul] at h2
    rw [parInd_law, h1, map_zero, smul_zero]
  let H : Subgroup (GL n (ZMod p)) := Subgroup.map (parab (ZMod p) e).subtype
    (⨅ b : {b // b ≠ a}, ((Pi.evalMonoidHom (fun c => GL (m c) (ZMod p)) b.1).comp (leviProj (ZMod p) e)).ker)
  have hH : ∀ x : parab (ZMod p) e, (∀ b, b ≠ a → leviProj (ZMod p) e x b = 1) → (x : GL n (ZMod p)) ∈ H := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    intro b
    exact MonoidHom.mem_ker.2 (hx b.1 b.2)
  have hH' : ∀ y ∈ H, ∃ x : parab (ZMod p) e, (x : GL n (ZMod p)) = y ∧
      ∀ b, b ≠ a → leviProj (ZMod p) e x b = 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf] at hx
    exact ⟨x, rfl, fun b hb => MonoidHom.mem_ker.1 (hx ⟨b, hb⟩)⟩
  have key : ∀ y ∈ H, ∀ w, Λ (ρ y w) = ((θ.comp GeneralLinearGroup.det y : ℂˣ) : ℂ) • Λ w := by
    intro y hy w
    obtain ⟨x, rfl, hx⟩ := hH' y hy
    obtain ⟨h, hh, hl⟩ := exists_canon_lift hp (x : GL n (ZMod p))
    have hP : h ∈ parab F e := mem_parab.2 fun i j hij => by
      have h0 := mem_parab.1 x.2 i j hij
      change h.val i j = 0
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) i j).val : F) = 0
      rw [h0]
      simp
    let q : parab F e := ⟨h, hP⟩
    have hq : ∀ b, b ≠ a → leviProj F e q b = 1 := by
      intro b hb
      have h2 := hx b hb
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h3 := congrArg (fun g : GL (m b) (ZMod p) => (g : Matrix (m b) (m b) (ZMod p)) i j) h2
      simp only [leviProj_apply] at h3
      rw [leviProj_apply]
      change h.val _ _ = _
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) _ _).val : F) = _
      rw [h3]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.val_one]
    have hqa : leviProj F e q = Pi.mulSingle a (leviProj F e q a) := by
      funext b
      by_cases hb : b = a
      · subst hb; simp
      · rw [Pi.mulSingle_eq_of_ne hb, hq b hb]
    have hKa : leviProj F e q a ∈ KO F (m a) := by
      refine IsLift.mem_KO hp (g := leviProj (ZMod p) e x a) fun i j => ?_
      change valuation F (h.val _ _ - _) < 1
      rw [hh]
      simp
    have hδ : deltaHalf F m (leviProj F e q) = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ ?_
      by_cases hb : b = a
      · subst hb; exact valuation_det_of_mem_KO hKa
      · rw [hq b hb, map_one]; simp
    have hdet : χ (GeneralLinearGroup.det (leviProj F e q a)) = θ (GeneralLinearGroup.det (x : GL n (ZMod p))) := by
      rw [← CharLift.det hp hθ hl]
      congr 1
      change _ = GeneralLinearGroup.det (q : GL n F)
      rw [det_parab F e q, Finset.prod_eq_single a]
      · intro b _ hb; rw [hq b hb, map_one]
      · simp
    have hv := hint _ h hl w
    rw [hΛ, hΛ, ← hv]
    change (φ w).1.1 (1 * h) = _
    rw [one_mul]
    have hlaw := parInd_law e (piTensor s) (φ w) q 1
    rw [mul_one] at hlaw
    change (φ w).1.1 (q : GL n F) = _
    rw [hlaw, hδ, Units.val_one, one_smul, hqa, piTensor_mulSingle s a _ _ (hs _ hKa), MonoidHom.comp_apply, hdet]
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_map ρ H (θ.comp GeneralLinearGroup.det) Λ hΛ0 key
  exact ⟨v, hv0, fun x hx => hv _ (hH x hx)⟩

end GlobalTheory.LevelType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardTypeVectorOfParabolicTypeVector
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LevelType
open Matrix

theorem exists_stdVec_of_parVec : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ Fin r) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL (Fin r) (ZMod p)) U) (v : U), Fintype.card (m a) = 1 → v ≠ 0 → ParVec ρ e a θ v → ∃ (c : ℕ) (v' : U), c < r ∧ v' ≠ 0 ∧ StdVec ρ c θ v' := by
  intro p _ r α _ _ m _ _ e a θ U _ _ ρ v hm hv hpar
  obtain ⟨k0⟩ : Nonempty (m a) := Fintype.card_pos_iff.1 (by omega)
  let σ := Tuple.sort (blk e)
  let i₀ := e ⟨a, k0⟩
  have hi₀ : blk e i₀ = a := blk_apply e a k0
  have hmono := Tuple.monotone_sort (blk e)
  have hlt : ∀ i, blk e i < a → σ.symm i < σ.symm i₀ := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i)) < blk e (σ (σ.symm i₀))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hgt : ∀ i, a < blk e i → σ.symm i₀ < σ.symm i := fun i h => hmono.reflect_lt (by
    show blk e (σ (σ.symm i₀)) < blk e (σ (σ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hi₀]; exact h)
  have hlo : ∀ i, (σ.symm i).val ≤ (σ.symm i₀).val → blk e i ≤ a := fun i h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hgt i (not_le.1 h'))))
  have hhi : ∀ j, (σ.symm i₀).val ≤ (σ.symm j).val → a ≤ blk e j := fun j h => by
    by_contra h'
    exact absurd h (not_le.2 (Fin.lt_def.1 (hlt j (not_le.1 h'))))
  refine ⟨(σ.symm i₀).val, ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm) v, (σ.symm i₀).isLt, ?_, ?_⟩
  · intro h0
    apply hv
    have := congrArg (ρ (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹) h0
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at this
  · intro x hx
    set y := (GlobalTheory.Parabolic.permGL (ZMod p) σ.symm)⁻¹ * x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm with hy
    have hyij : ∀ i j, ¬ (blk e i ≤ a ∧ a ≤ blk e j) → y.val i j = if i = j then 1 else 0 := by
      intro i j hij
      have hyv : y.val i j = x.val (σ.symm i) (σ.symm j) := by
        rw [← GlobalTheory.Parabolic.conj_permGL_apply σ.symm y i j, hy]
        congr 2
        group
      rw [hyv, hx _ _ (fun h => hij ⟨hlo i h.1, hhi j h.2⟩)]
      simp
    have hyP : y ∈ parab (ZMod p) e := mem_parab.2 fun i j hji => by
      rw [hyij i j (fun h => absurd (h.1.trans h.2) (not_le.2 hji)), if_neg]
      rintro rfl
      exact lt_irrefl _ hji
    have hlev : ∀ b, b ≠ a → leviProj (ZMod p) e ⟨y, hyP⟩ b = 1 := by
      intro b hb
      refine Units.ext (Matrix.ext fun k l => ?_)
      rw [leviProj_apply, Units.val_one]
      rw [hyij _ _ (fun h => hb (le_antisymm (by simpa using h.1) (by simpa using h.2)))]
      simp [Matrix.one_apply]
    have h1 := hpar ⟨y, hyP⟩ hlev
    change ρ y v = (θ (GeneralLinearGroup.det y) : ℂ) • v at h1
    have hdet : GeneralLinearGroup.det y = GeneralLinearGroup.det x := by
      rw [hy, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    have hxP : x * GlobalTheory.Parabolic.permGL (ZMod p) σ.symm = GlobalTheory.Parabolic.permGL (ZMod p) σ.symm * y := by rw [hy]; group
    rw [← Module.End.mul_apply, ← map_mul, hxP, map_mul, Module.End.mul_apply, h1, hdet, map_smul]

end GlobalTheory.LevelType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramified
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem gl_lc_sc (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (r : ℕ) :
    LocallyCompactSpace (GL (Fin r) F) ∧ SecondCountableTopology (GL (Fin r) F) := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin r) (Fin r) F)).symm.secondCountableTopology
  exact ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

theorem gl_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (letI := M.mG; M.μG.IsMulRightInvariant) := by
  intro F E _ _ _ _ hU r M
  haveI : LocallyCompactSpace F := hU.lcF
  obtain ⟨h1, h2⟩ := gl_lc_sc F r
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  have hmod : ∀ a : GL (Fin r) F, Measure.modularCharacterFun a = 1 := by
    intro a
    refine GlobalTheory.SplitFlip.hom_eq_one_of_center
      (Measure.modularCharacter : GL (Fin r) F →* NNReal) (fun z hz => ?_) a
    change Measure.modularCharacterFun z = 1
    have e : Measure.map (fun x : GL (Fin r) F => x * z)
        (Measure.haar : Measure (GL (Fin r) F)) = Measure.haar := by
      rw [show (fun x : GL (Fin r) F => x * z) = fun x => z * x from
        funext fun x => (hz x).symm, map_mul_left_eq_self]
    rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure (GL (Fin r) F)) z]
    simp only [e, Measure.haarScalarFactor_self]
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) M.μG) M.μG,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, hmod, one_smul]

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.Pst.PstBridge

open GlobalTheory.Pst GlobalTheory.Pst.BridgeParam Formalism.MainNotions.N Module

section Rank

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem rank_le_of_conj {K K' : FinExt l} {g : GQ l} {ρ : Representation LL ↥(GK K) V}
    {ρ' : Representation LL ↥(GK K') V}
    (hρ : ∀ (h : ↥(GK K)) (h' : ↥(GK K')), (h' : GQ l) = g * h * g⁻¹ → ρ' h' = ρ h)
    (hK : ∀ x, x ∈ K.1 ↔ g x ∈ K'.1) :
    Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ') := by
  have hρ' : ∀ (h' : ↥(GK K')) (h : ↥(GK K)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ → ρ h = ρ' h' :=
    fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
  have hK' : ∀ x, x ∈ K'.1 ↔ g⁻¹ x ∈ K.1 := fun x => by
    rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  let i : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l) := fun c => ⟨g c, (BridgeInd.mem_Kur_iff g _).1 c.2⟩
  have hi : Function.Surjective i := fun c =>
    ⟨⟨g⁻¹ c, (BridgeInd.mem_Kur_iff g _).2 (by rw [show g (g⁻¹ (c : Om l)) = c from g.apply_symm_apply _]; exact c.2)⟩,
      Subtype.ext (g.apply_symm_apply _)⟩
  let j : DpstUr P ρ →+ DpstUr P ρ' :=
    (toUr P ρ').toAddMonoidHom.comp ((conjD P hρ hK).toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom)
  have hj : Function.Injective j := by
    intro x y hxy
    have hx : ∀ z : ↥(Dpst P ρ), conjD P hρ' hK' (conjD P hρ hK z) = z := fun z =>
      Subtype.ext (by
        have := LinearMap.congr_fun (conjV_conjV_inv P (LL := LL) (V := V) g⁻¹) z.1
        rw [inv_inv] at this
        exact this)
    have := congrArg (conjD P hρ' hK') hxy
    exact (hx x).symm.trans (this.trans (hx y))
  refine rank_le_of_surjective_injective i j hi hj fun c x => ?_
  exact conjD_mulD P hρ hK c (i c) rfl x

end Rank

theorem isPstAt_indep_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  intro l _ P AI _ E Ω _ _ _ _ _ A O O' _ _ _ _ _ _ Bw Bw' hj hj' a r _ hr
  obtain ⟨L₁, r₁, hm₁, hV₁⟩ := hr
  let L₂ : FinExt l := supExt L₁ Bw'.LL
  have h₁ : L₁.1 ≤ L₂.1 := le_sup_left
  have h₂ : Bw'.LL.1 ≤ L₂.1 := le_sup_right
  let r₂ := mapRep (IntermediateField.inclusion h₁).toRingHom r₁
  have hW := GlobalTheory.PstExt.isPst_enlarge P Bw h₁ r₁ hV₁
  obtain ⟨g, hg, hK⟩ := BridgeInd.exists_conj Bw Bw' hj hj'
  have hρ := BridgeInd.repE_conj Bw Bw' hg L₂ r₂
  refine ⟨L₂, r₂, ⟨h₂, ?_⟩, ?_⟩
  · rw [← hm₁.2]
    ext x i k
    rfl
  · have e1 := rank_le_of_conj P hρ hK
    have hρ' : ∀ (h' : ↥(GK Bw'.Kw)) (h : ↥(GK Bw.Kw)), (h : GQ l) = g⁻¹ * h' * g⁻¹⁻¹ →
        Bw.repE L₂ r₂ h = Bw'.repE L₂ r₂ h' :=
      fun h' h hh => (hρ h h' (by rw [hh]; group)).symm
    have hK' : ∀ x, x ∈ Bw'.Kw.1 ↔ g⁻¹ x ∈ Bw.Kw.1 := fun x => by
      rw [hK, show g (g⁻¹ x) = x from g.apply_symm_apply x]
    have e2 := rank_le_of_conj P hρ' hK'
    unfold IsPst at hW ⊢
    rw [← hW]
    exact le_antisymm e2 e1

end GlobalTheory.Pst.PstBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientRepresentationTwoReindexings
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem reix_eq_conj (R : Type) [CommRing R] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) : ∃ w : GL n R, ∀ g : GL m R, reix R φ g * w = w * reix R φ' g := by
  let e : n ≃ n := φ'.symm.trans φ
  have h1 : ((e.symm.toPEquiv.toMatrix : Matrix n n R) * e.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  have h2 : ((e.toPEquiv.toMatrix : Matrix n n R) * e.symm.toPEquiv.toMatrix) = 1 := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  let w : GL n R := ⟨e.symm.toPEquiv.toMatrix, e.toPEquiv.toMatrix, h1, h2⟩
  refine ⟨w, fun g => ?_⟩
  have key : (reix R φ g).val = w.val * (reix R φ' g).val * w⁻¹.val := by
    change _ = e.symm.toPEquiv.toMatrix * _ * e.toPEquiv.toMatrix
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    simp [val_reix, e]
  apply Units.ext
  rw [Units.val_mul, key, mul_assoc, Units.inv_mul, mul_one, Units.val_mul]

theorem subquotient_reix (R : Type) [CommRing R] (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ φ' : m ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL n R) V) :
    IsSubquotient (σ.comp (reix R φ) : Representation ℂ (GL m R) V) (σ.comp (reix R φ') : Representation ℂ (GL m R) V) := by
  obtain ⟨w, hw⟩ := reix_eq_conj R φ φ'
  refine IsSubquotient.of_surjective ⟨σ w, fun g => ?_⟩ fun v => ⟨σ w⁻¹ v, ?_⟩
  · change σ w * σ (reix R φ' g) = σ (reix R φ g) * σ w
    rw [← map_mul, ← map_mul, hw]
  · change σ w (σ w⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.LevelType
end

