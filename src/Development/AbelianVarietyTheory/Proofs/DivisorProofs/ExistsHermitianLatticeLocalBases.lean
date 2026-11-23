module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TripleSpaceW

open scoped ComplexOrder

theorem hasSig_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by simpa using (Fintype.card_congr e).symm, (P.1.submatrix e id).map star, ?_⟩
  have hJ : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := rfl
  rw [hJ, ← hP]
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, Formalism.UG.cT,
    Matrix.reindex_apply, star_star]
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  · rw [← e.symm.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [e.apply_symm_apply]; rfl
  · rw [e.apply_symm_apply]

theorem isCartan_map_conj {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (G.map (starRingEnd ℂ)) s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun x hx => ?_⟩
  · have := congrArg (fun A : Matrix (Fin k) (Fin k) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    rw [← this]
    congr 2
    ext a b
    simp [Matrix.conjTranspose_apply]
  · have hsG : sᴴ * G = G * s := by
      calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
        _ = G * s := by rw [← Matrix.mul_assoc, h2]
    have e1 : (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
      calc (s *ᵥ x) ⬝ᵥ G.map (starRingEnd ℂ) *ᵥ star x = (s *ᵥ x) ⬝ᵥ star (G *ᵥ x) := by
            congr 1; ext a; simp [Matrix.mulVec, dotProduct, star_sum]
        _ = star (star (s *ᵥ x) ⬝ᵥ G *ᵥ x) := by rw [Matrix.star_dotProduct, star_star, dotProduct_comm]
        _ = star (star x ⬝ᵥ (G * s) *ᵥ x) := by
            rw [← hsG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star x) sᴴ, ← Matrix.star_mulVec]
    have := h3.dotProduct_mulVec_pos hx
    rw [e1, Complex.star_def, Complex.conj_re]
    exact (Complex.lt_def.1 this).1

section ConjLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def conjO (r : 𝓞 E) : 𝓞 E := ⟨star (r : E), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩

theorem coe_conjO (r : 𝓞 E) : ((conjO r : 𝓞 E) : E) = star (r : E) := rfl

theorem star_smulO (r : 𝓞 E) (y : Fin n → E) : star (r • y) = conjO r • star y := by
  ext i
  simp only [Pi.star_apply, Pi.smul_apply, Algebra.smul_def, star_mul']
  rfl

def conjSub (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | star y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, star_add] at ha hb ⊢; exact Λ.add_mem ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, star_zero]; exact Λ.zero_mem
  smul_mem' := fun r y hy => by
    have e : star (r • y) = conjO r • star y := star_smulO r y
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [e]; exact Λ.smul_mem _ hy

theorem mem_conjSub {Λ : Submodule (𝓞 E) (Fin n → E)} {y : Fin n → E} : y ∈ conjSub Λ ↔ star y ∈ Λ := Iff.rfl

theorem star_mem_span {R : Type} [CommRing R] [Module R (Fin n → E)] (c : R → R)
    (hc : ∀ (r : R) (y : Fin n → E), star (r • y) = c r • star y) {s : Set (Fin n → E)} {y : Fin n → E}
    (hy : y ∈ Submodule.span R s) : star y ∈ Submodule.span R (star '' s) := by
  induction hy using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [star_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [hc]; exact Submodule.smul_mem _ _ hx

theorem star_smulE (r : E) (y : Fin n → E) : star (r • y) = star r • star y := by
  ext i; simp [star_mul']

theorem conjSub_isLattice {Λ : Submodule (𝓞 E) (Fin n → E)} (h : Λ.IsLattice E) : (conjSub Λ).IsLattice E := by
  obtain ⟨S, hS⟩ := h.fg
  have e : conjSub Λ = Submodule.span (𝓞 E) (star '' (S : Set (Fin n → E))) := by
    refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
    · have := star_mem_span conjO star_smulO (hS ▸ (mem_conjSub.1 hy))
      rwa [star_star] at this
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_conjSub, star_star, ← hS]
      exact Submodule.subset_span hx
  apply Submodule.IsLattice.of_fg E
  rw [e, Submodule.fg_def]
  exact ⟨_, S.finite_toSet.image _, rfl⟩

theorem conjSub_isFullLattice {Λ : Submodule (𝓞 E) (Fin n → E)} (h : Λ.IsFullLattice E) :
    (conjSub Λ).IsFullLattice E := by
  haveI : (conjSub Λ).IsLattice E := conjSub_isLattice h.toIsLattice
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro y _
  have hy : star y ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [h.span_eq_top]; trivial
  have hy' := star_mem_span star star_smulE hy
  have heq : star '' (Λ : Set (Fin n → E)) = (conjSub Λ : Set (Fin n → E)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change star (star x) ∈ Λ
      simpa only [star_star, SetLike.mem_coe] using hx
    · intro hz
      exact ⟨star z, mem_conjSub.mp hz, star_star z⟩
  simpa only [star_star, heq] using hy' 

theorem exists_coe_iff (z : E) : (∃ b : 𝓞 E, (b : E) = z) ↔ IsIntegral ℤ (star z) := by
  refine ⟨fun ⟨b, hb⟩ => hb ▸ (RingOfIntegers.isIntegral_coe b).map (starRingEnd E).toIntAlgHom, fun h => ?_⟩
  have h' : IsIntegral ℤ z := by simpa [starRingEnd_apply] using h.map (starRingEnd E).toIntAlgHom
  exact ⟨⟨z, h'⟩, rfl⟩

end ConjLat

end GlobalTheory.TripleSpaceW

namespace GlobalTheory.FunObj

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem isHerm_spaceW : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin (spW G i j).rank → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin (spW G i j).rank) (Fv D.host.F v)),
      Spc.IsHerm D.sp.cm.sig B
        (Spc.mk ((1 : D.host.E) • (spW G i j).gram) Λ (fun w => W.cart (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) (τf w)) bas)
        ((spW G i j).rank - (D.R.m - j - 1) / 2) ((D.R.m - j - 1) / 2) := by
  intro D T L sc G μ₀ hL W i j B τf hemb
  have hX : (Node.grid ((i : ℕ) + 1) ((j : ℕ) + 1)).InRange D.R.m := ⟨i.2, j.2⟩
  have hV := node_isV G hL hX
  haveI hlat : (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))).IsLattice D.host.E :=
    GlobalTheory.TripleSpaceW.conjSub_isLattice hV.sd.1
  haveI := GlobalTheory.TripleSpaceW.conjSub_isFullLattice (selfDual_isFullLattice _ _ hV.sd)
  have hex : ∀ v : B.P, ∃ bas : GL (Fin (spW G i j).rank) (Fv D.host.F v.1),
      GlobalTheory.AdelicU.IsSplitBasis (B.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)))) bas := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))))
      (GlobalTheory.AdelicU.isCMExt_host D)
  choose bas0 hbas0 using hex
  have hq : Node.neg D.R.m (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) = (D.R.m - j - 1) / 2 := by
    show (D.R.m - ((j : ℕ) + 1)) / 2 = _
    rw [Nat.sub_sub]
  have hherm : ∀ a b, star ((spW G i j).gram b a) = (spW G i j).gram a b := fun a b =>
    (spW G i j).herm.eq ((spW G i j).frame b) ((spW G i j).frame a)
  refine ⟨GlobalTheory.TripleSpaceW.conjSub (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))),
    fun v => if h : v ∈ B.P then bas0 ⟨v, h⟩ else 1, ⟨fun a b => ?_, fun w => ?_, GlobalTheory.TripleSpaceW.conjSub_isFullLattice (selfDual_isFullLattice _ _ hV.sd), fun y => ?_, fun w => ?_, fun v => ?_⟩⟩
  · show star (((1 : D.host.E) • (spW G i j).gram) b a) = ((1 : D.host.E) • (spW G i j).gram) a b
    rw [one_smul]
    exact hherm a b
  · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _ _
    have hs := hV.sigOK (B.emb w).1
    rw [hV.sig, hq, ← hV.rank] at hs
    rw [one_smul]
    exact GlobalTheory.TripleSpaceW.hasSig_of_hasSignature hs
  · have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
    have hh' : ∀ a b, star ((spW G i j).gram a b) = (spW G i j).gram b a := fun a b => hherm b a
    have key : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((1 : D.host.E) • (spW G i j).gram) y x =
        star (∑ a, ∑ b, star ((star x) a) * (spW G i j).gram a b * (star y) b) := fun x => by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, one_smul, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
        Pi.star_apply, hσ, hh', Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    show star y ∈ G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ↔ _
    rw [hV.sd.2 (star y)]
    constructor
    · intro h x hx
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff]
      exact h _ hx
    · intro h x' hx'
      have := h (star x') (by rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx')
      rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff, star_star] at this
      exact this
  · have e : ((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1 =
        (gramAt D (spW G i j) (τf w)).map (starRingEnd ℂ) := by
      ext a b
      simp only [one_smul, Matrix.map_apply, hemb, gramAt]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((1 : D.host.E) • (spW G i j).gram).map (B.emb w).1) _
    rw [e]
    exact GlobalTheory.TripleSpaceW.isCartan_map_conj (W.cart_is _ hX (τf w))
  · show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) _ (if h : v.1 ∈ B.P then bas0 ⟨v.1, h⟩ else 1)
    rw [dite_eq_left v.2]
    exact hbas0 v

end GlobalTheory.FunObj
