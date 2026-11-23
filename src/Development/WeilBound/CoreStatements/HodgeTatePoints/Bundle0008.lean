module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0015
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CompMemAddFun
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

section

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
lemma comp_mem_addFun (p : ℕ) (e : X ≃+ Y) {f : Y → C} (hf : f ∈ addFun R p Y) :
    (fun x => f (e x)) ∈ addFun R p X := by
  have h : ∀ a b : Y, f (a + b) - f a - f b ∈ pInt R p := hf
  show ∀ a b : X, f (e (a + b)) - f (e a) - f (e b) ∈ pInt R p
  intro a b
  rw [map_add (f := _)]
  exact h (e a) (e b)

private theorem map_pbE_eq_of_addEquiv (e : X ≃+ Y) (SX : Submodule R (X → C)) (SY : Submodule R (Y → C))
    (h1 : ∀ f ∈ SY, (fun x => f (e x)) ∈ SX) (h2 : ∀ g ∈ SX, (fun y => g (e.symm y)) ∈ SY) :
    SY.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = SX := by
  ext g
  rw [Submodule.mem_map_equiv]
  constructor
  · intro h
    have h3 := h1 _ h
    convert h3 using 1
    funext x
    rw [pbE_symm_apply]
    simp
  · intro h
    convert h2 g h using 1
    funext y
    exact pbE_symm_apply e g y

lemma map_addFun (p : ℕ) (e : X ≃+ Y) :
    (addFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = addFun R p X := by
  exact map_pbE_eq_of_addEquiv e _ _ (fun f hf => comp_mem_addFun p e hf) (fun g hg => comp_mem_addFun p e.symm hg)

lemma map_intFun (e : X ≃+ Y) :
    (intFun R Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = intFun R X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    have h : ∀ y : Y, ∃ r : R, algebraMap R C r = f y := hf
    show ∀ x : X, ∃ r : R, algebraMap R C r = f (e x)
    exact fun x => h (e x)
  · intro g hg
    have h : ∀ x : X, ∃ r : R, algebraMap R C r = g x := hg
    show ∀ y : Y, ∃ r : R, algebraMap R C r = g (e.symm y)
    exact fun y => h (e.symm y)

lemma map_pFun (p : ℕ) (e : X ≃+ Y) :
    (pFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = pFun R p X := by
  refine map_pbE_eq_of_addEquiv e _ _ ?_ ?_
  · intro f hf
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hf ⊢
    exact fun x => hf (e x)
  · intro g hg
    simp only [pFun, Submodule.mem_pi, Set.mem_univ, true_implies] at hg ⊢
    exact fun y => hg (e.symm y)

lemma map_afFun (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (afFun p M).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      afFun p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
  show Submodule.map _ (M ⊓ addFun R p Y) = _ ⊓ addFun R p X
  rw [Submodule.map_inf, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

lemma map_linFun (p : ℕ) (e : X ≃+ Y) :
    (linFun R p Y).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) = linFun R p X := by
  show Submodule.map _ (intFun R Y ⊓ addFun R p Y) = intFun R X ⊓ addFun R p X
  rw [Submodule.map_inf, map_intFun, map_addFun]
  exact (pbE (C := C) (R := R) e).injective

private theorem nonempty_quotient_linearEquiv_map {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V ≃ₗ[R] W) (L A : Submodule R V) :
    Nonempty ((↥L ⧸ Submodule.comap L.subtype A) ≃ₗ[R]
      (↥(L.map (φ : V →ₗ[R] W)) ⧸ Submodule.comap (L.map (φ : V →ₗ[R] W)).subtype (A.map (φ : V →ₗ[R] W)))) := by
  refine ⟨Submodule.Quotient.equiv _ _ (φ.submoduleMap L) ?_⟩
  ext ⟨w, hw⟩
  constructor
  · rintro ⟨⟨v, hv⟩, hvA, hvw⟩
    have hw' : φ v = w := congrArg Subtype.val hvw
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hvA ⊢
    exact ⟨v, hvA, hw'⟩
  · intro h
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at h
    obtain ⟨v, hvA, rfl⟩ := h
    obtain ⟨v', hv'L, hv'⟩ := hw
    have hvv : v' = v := φ.injective hv'
    subst hvv
    exact ⟨⟨v', hv'L⟩, hvA, rfl⟩

lemma afQuot_equiv (p : ℕ) (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    Nonempty (AFQuot p M ≃ₗ[R]
      AFQuot p (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)))) := by
  obtain ⟨f⟩ := nonempty_quotient_linearEquiv_map (pbE (C := C) (R := R) e) (linFun R p Y) (afFun p M ⊔ pFun R p Y)
  rw [map_linFun, Submodule.map_sup, map_afFun, map_pFun] at f
  exact ⟨f⟩

end

lemma exists_coord (p : ℕ) [Fact p.Prime] (N : Type) [AddCommGroup N] [Finite N]
    [Module (ZMod p) N] : ∃ n : ℕ, Nonempty ((Fin n → ZMod p) ≃+ N) :=
  have : Module.Finite (ZMod p) N := Module.Finite.of_finite
  ⟨_, ⟨(Module.finBasis (ZMod p) N).equivFun.symm.toAddEquiv⟩⟩

private theorem genAF_bot_of_span_monomials {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
    {N : Type} [AddCommGroup N] (p : ℕ) {ι : Type} [Fintype ι] (M : Submodule R (N → C))
    (y : ι → N → C) (hy : ∀ j, y j ∈ afFun p M) (S : Set (N → C))
    (hS : M = Submodule.span R S) (hgen : ∀ s ∈ S, ∃ α : ι → ℕ, s = ∏ j, y j ^ α j) :
    GenAF p M ⊥ := by
  have hinv : invFun M (⊥ : AddSubgroup N) = M := by
    ext g
    constructor
    · intro h
      exact (show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x from h).1
    · intro h
      show g ∈ M ∧ ∀ x k : N, k ∈ (⊥ : AddSubgroup N) → g (x + k) = g x
      refine ⟨h, ?_⟩
      intro x k hk
      rw [AddSubgroup.mem_bot] at hk
      subst hk
      simp
  show invFun M ⊥ ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p (invFun M ⊥) : Set (N → C)))
  rw [hinv]
  have hsp : Submodule.span R S ≤ Subalgebra.toSubmodule (Algebra.adjoin R (afFun p M : Set (N → C))) := by
    rw [Submodule.span_le]
    intro s hs
    obtain ⟨α, rfl⟩ := hgen s hs
    exact (Subalgebra.mem_toSubmodule _).mpr
      (Subalgebra.prod_mem _ (fun j _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (hy j)) _))
  intro g hg
  rw [hS] at hg
  exact hsp hg

theorem cnt_of (hcoord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) := by
  intro p _ C _ _ _ v R _ _ hvR hp N _ _ _ hN AA cA cN hA hC
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  obtain ⟨n, ⟨e⟩⟩ := exists_coord p N
  have hcard : Fintype.card (Fin n → ZMod p) = Fintype.card N := Fintype.card_congr e.toEquiv
  obtain ⟨f⟩ := afQuot_equiv (C := C) (R := R) p e AA.carrier
  have hA' : HasLen v R (AFQuot p (hopfPull e AA).carrier) cA := by
    obtain ⟨m, c, ⟨g⟩, hc⟩ := hA
    exact ⟨m, c, ⟨f.symm.trans g⟩, hc⟩
  have hC' : HasColen R v (hopfPull e AA).carrier cN := hasColen_map v e _ _ hC
  obtain ⟨hle, heq⟩ := hcoord p C v R hvR hp (Fin n) (hopfPull e AA) cA cN hA' hC'
  rw [hcard] at hle heq
  refine ⟨hle, fun hE => ?_⟩
  obtain ⟨x, hxj, hspan⟩ := heq hE
  refine genAF_bot_of_span_monomials p AA.carrier (fun j z => x j (e.symm z)) ?_
    ((⇑(pbE (C := C) (R := R) e.symm)) '' Set.range
      (fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)) ?_ ?_
  · intro j
    have hx' : x j ∈ (afFun p AA.carrier).map
        (pbE (C := C) (R := R) e : (N → C) →ₗ[R] ((Fin n → ZMod p) → C)) := by
      rw [map_afFun]
      exact hxj j
    have h2 := (Submodule.mem_map_equiv _).mp hx'
    convert h2 using 1
    funext z
    rw [pbE_symm_apply]
  · have h1 := Submodule.map_span (pbE (C := C) (R := R) e.symm : ((Fin n → ZMod p) → C) →ₗ[R] (N → C))
      (Set.range fun (α : Fin n → ZMod p) (y : Fin n → ZMod p) => ∏ j, x j y ^ (α j).val)
    rw [← hspan] at h1
    rw [← map_pbE_symm e AA.carrier]
    exact h1
  · rintro s ⟨_, ⟨α, rfl⟩, rfl⟩
    refine ⟨fun j => (α j).val, ?_⟩
    funext z
    rw [Finset.prod_apply]
    rfl

end PositivityTheory.HtPt.Ra
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] {ρ : O → V →ₗ[K] V} {χ : O → K} {x : V} :
    x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eig, sub_eq_zero]

theorem eig_frob : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  intro K _ p _ _ d O ρ χ
  apply le_antisymm
  · classical
    intro y hy
    rw [mem_eig] at hy
    set K0 := (frobenius K p).fieldRange with hK0
    let β := Module.Basis.ofVectorSpace K0 K
    have hpow : ∀ c : K, c ^ p ∈ K0 := fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩
    have hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι := by
      intro c u ι
      have h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u := rfl
      rw [h0, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K) := by
      intro ι f
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finsupp.finsetSum_apply]
    let z : _ → Fin d → K := fun ι j => (β.repr (y j) ι : K)
    have hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r := by
      intro ι a r
      have h1 := congrFun (hy a) r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := congrArg (fun u => (β.repr u ι : K)) h1
      simp only [hsum, hrepr] at h2
      exact h2
    have hex : ∀ ι j, ∃ x : K, x ^ p = z ι j := by
      intro ι j
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (β.repr (y j) ι).2
      exact ⟨x, by rw [← frobenius_def]; exact hx⟩
    choose x hx using hex
    have hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ := by
      intro ι
      rw [mem_eig]
      intro a
      funext r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      apply frobenius_inj K p
      rw [frobenius_def, frobenius_def, sum_pow_char, mul_pow]
      simp only [mul_pow, hx]
      exact hz ι a r
    let T := Finset.univ.biUnion fun j => (β.repr (y j)).support
    have hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι) := by
      funext j
      rw [Finset.sum_apply]
      conv_lhs => rw [← β.linearCombination_repr (y j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p
      rw [hx ι j, mul_comm]
    rw [hT, frobSub]
    exact Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)
  · rw [frobSub, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eig]
    rw [SetLike.mem_coe, mem_eig] at hx
    intro a
    have hxa := hx a
    simp only [Matrix.toLin'_apply] at hxa ⊢
    funext r
    have h1 := congrFun hxa r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢
    rw [← mul_pow, ← h1, sum_pow_char]
    simp only [mul_pow]

theorem eig_dual : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s
  let ρL : O →+* Module.End K (Fin d → K) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ
  obtain ⟨e, he_hom, he_mem, he_id, -, he_comb⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Crv.SplitProj.split_proj K C (Fin d → K) L O k S χ hχ hv ρL hL hρ
  obtain ⟨m, c, b, hc, hes⟩ := he_comb s
  set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW
  set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'
  set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE
  have hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, map_sum]
    simp only [map_smul]
  have hlinT : Matrix.toLin' E.transpose =
      ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE, Matrix.transpose_sum, map_sum]
    simp only [Matrix.transpose_smul, map_smul]
  have heE : ∀ x, e s x = E.mulVec x := by
    intro x
    rw [← Matrix.toLin'_apply, hlin, hes]
    rfl
  have hEW : ∀ x, E.mulVec x ∈ W := fun x => heE x ▸ he_mem s x
  have hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i := fun i x hx => heE x ▸ he_hom s i x hx
  have hEid : ∀ x ∈ W, E.mulVec x = x := fun x hx => (heE x).symm.trans (he_id s x hx)
  have hETid : ∀ y ∈ W', E.transpose.mulVec y = y := by
    intro y hy
    simp only [hW', mem_eig, Matrix.toLin'_apply] at hy
    rw [← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul,
      ← Finset.sum_smul, ← map_sum]
    rw [hc s, if_pos rfl, map_one, one_smul]
  have hETW : ∀ z, E.transpose.mulVec z ∈ W' := by
    intro z
    rw [hW', mem_eig]
    intro a
    have hmat : ρ a * E = algebraMap k K (χ s a) • E := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec]
      have h1 := (mem_eig.1 (hEW w)) a
      simpa only [Matrix.toLin'_apply] using h1
    have h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose := by
      have hcm : E * ρ a = ρ a * E := by
        rw [hE, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]
      rw [← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]
    show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) =
      algebraMap k K (χ s a) • E.transpose.mulVec z
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul,
      LinearMap.smul_apply, Matrix.toLin'_apply]
  have hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  let B : W →ₗ[K] W' →ₗ[K] K := (dotProductBilin K K).compl₁₂ W.subtype W'.subtype
  have hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K) := fun x y => rfl
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun x hx => ?_
    have h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0 := by
      intro z
      have h1 : B x ⟨_, hETW z⟩ = 0 := by rw [hx]; rfl
      rw [hB] at h1
      change (x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1
      rwa [hadj, hEid _ x.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hinj2 : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    have h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0 := by
      intro z
      have h1 : B.flip y ⟨_, hEW z⟩ = 0 := by rw [hy]; rfl
      rw [LinearMap.flip_apply, hB] at h1
      change E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1
      rwa [← hadj, hETid _ y.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W' := Subspace.dual_finrank_eq
  have hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  have hle1 := LinearMap.finrank_le_finrank_of_injective hinj
  have hle2 := LinearMap.finrank_le_finrank_of_injective hinj2
  have hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K) := by omega
  have hbij : Function.Bijective B :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩
  obtain ⟨-, hdeg, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C W W' (sub C L W) B (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C _ L W hL).1 hbij
  have hident : dualLat C (sub C L W) B = sub C (dotDual C L) W' := by
    funext i
    ext y
    show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1
    constructor
    · intro h x hx
      have hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y := by
        rw [hB]
        show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)
        rw [← hadj, hETid _ y.2]
      rw [hxy]
      exact h _ (hEL i x hx)
    · intro h x hx
      exact h x hx
  show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)
  rw [← hident]
  exact hdeg

end PositivityTheory.HtPt.Ci
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcTors
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

section
variable {S Y : Scheme.{0}} {G : Over S} [GrpObj G]

theorem mul_congr {a b : Y ⟶ S} (h : a = b) (g k : Over.mk a ⟶ G) (g' k' : Over.mk b ⟶ G) (e : g.left = g'.left)
    (e' : k.left = k'.left) : (g * k).left = (g' * k').left := by
  subst h
  rw [Over.OverMorphism.ext e, Over.OverMorphism.ext e']

theorem comp_pow_pt {A B : Over S} (ψ : A ⟶ B) (g : B ⟶ G) (n : ℕ) : ψ ≫ g ^ n = (ψ ≫ g) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T}
  {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem tors_of_pt (h : Γ.IsTorsionAlong G x N i) (v : Y ⟶ Γ.G.left) {c : Y ⟶ S} (g : Over.mk c ⟶ G)
    (e : g.left = v ≫ i) : g ^ N = 1 := by
  have hc : c = (v ≫ Γ.G.hom) ≫ x := by
    rw [Category.assoc, ← h.isOver, ← Category.assoc, ← e]; exact (Over.w g).symm
  subst hc
  exact (h.kernel (Over.mk (v ≫ Γ.G.hom)) g).2 ⟨Over.homMk v rfl, e.symm⟩

theorem pt_of_tors (h : Γ.IsTorsionAlong G x N i) (b : Y ⟶ Spec (CommRingCat.of R)) {c : Y ⟶ S} (hc : c = b ≫ x)
    (g : Over.mk c ⟶ G) (hg : g ^ N = 1) : ∃ v : Y ⟶ Γ.G.left, v ≫ Γ.G.hom = b ∧ v ≫ i = g.left := by
  subst hc
  obtain ⟨y, hy⟩ := (h.kernel (Over.mk b) g).1 hg
  exact ⟨y.left, Over.w y, hy⟩

end

theorem torsion_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hsep R' _ _ φ Γ' i' h' B _ b j j' σ hj hjb hj'b hσ hσj hσj'
  let g : Over.mk (i' ≫ G.hom) ⟶ G := Over.homMk i' rfl
  obtain ⟨F, hF1, hF2⟩ := pt_of_tors h (Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (h'.isOver.trans (Category.assoc _ _ _).symm) g (tors_of_pt h' (𝟙 _) g (Category.id_comp _).symm)
  replace hF2 : F ≫ i = i' := hF2
  refine ⟨F, hF2, ?_, fun Y y z y₀ z₀ hy hz => ?_, ?_⟩
  · have hl : ∀ c : PullbackCone Γ.G.hom (Spec.map (CommRingCat.ofHom φ)), ∃ v : c.pt ⟶ Γ'.G.left,
        v ≫ F = c.fst ∧ v ≫ Γ'.G.hom = c.snd := fun c => by
      let k : Over.mk ((c.fst ≫ i) ≫ G.hom) ⟶ G := Over.homMk (c.fst ≫ i) rfl
      obtain ⟨v, h1, h2⟩ := pt_of_tors h' c.snd
        (by rw [Category.assoc, h.isOver, ← Category.assoc, c.condition, Category.assoc]) k (tors_of_pt h c.fst k rfl)
      exact ⟨v, tors_ext h (by rw [Category.assoc, hF1, ← Category.assoc, h1, c.condition])
        (by rw [Category.assoc, hF2, h2]; rfl), h1⟩
    choose l h1 h2 using hl
    exact ⟨⟨hF1⟩, ⟨PullbackCone.IsLimit.mk hF1 l h1 h2 fun c m a1 a2 => tors_ext h' (a2.trans (h2 c).symm) (by
      rw [← hF2, ← Category.assoc, ← Category.assoc, a1, h1])⟩⟩
  · have w : ∀ {y₀ : Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ⟶ Γ.G},
        (y₀.left ≫ i) ≫ G.hom = (Y.hom ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x := fun {y₀} => by
      rw [Category.assoc, h.isOver, ← Category.assoc, Over.w y₀]; rfl
    have w' : ∀ {y : Y ⟶ Γ'.G}, (y.left ≫ i') ≫ G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ x := fun {y} => by
      rw [Category.assoc, h'.isOver, ← Category.assoc, Over.w y]
    refine tors_ext h ?_ ?_
    · rw [Category.assoc, hF1, ← Category.assoc, Over.w (y * z)]
      exact Over.w (y₀ * z₀)
    · refine (h.mul _ y₀ z₀ (Over.homMk (y₀.left ≫ i) w) (Over.homMk (z₀.left ≫ i) w) rfl rfl).symm.trans ?_
      rw [Category.assoc, hF2]
      refine Eq.trans ?_ (h'.mul Y y z (Over.homMk (y.left ≫ i') w') (Over.homMk (z.left ≫ i') w') rfl rfl)
      refine mul_congr (Category.assoc _ _ _) _ _ _ _ ?_ ?_
      · show y₀.left ≫ i = y.left ≫ i'
        rw [hy, Category.assoc, hF2]
      · show z₀.left ≫ i = z.left ≫ i'
        rw [hz, Category.assoc, hF2]
  · have : IsDomain B := hj.isDomain j
    have : IsDominant (Spec.map (CommRingCat.ofHom j)) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)
      exact this⟩
    have hσ' : ∀ t, ∃ v : Spec (CommRingCat.of B) ⟶ Γ.G.left,
        v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom b) ∧ v ≫ i = σ t := fun t => by
      let k : Over.mk (σ t ≫ G.hom) ⟶ G := Over.homMk (σ t) rfl
      refine pt_of_tors h _ (hσ t) k ?_
      let ψ : Over.mk (Spec.map (CommRingCat.ofHom j) ≫ σ t ≫ G.hom) ⟶ Over.mk (σ t ≫ G.hom) :=
        Over.homMk (Spec.map (CommRingCat.ofHom j)) rfl
      have h1 : ψ ≫ k ^ N = ψ ≫ 1 := by
        rw [comp_pow_pt, MonObj.comp_one]
        exact tors_of_pt h (Γ.pt t).left _ (hσj t)
      exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of B)) G.hom
        ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom j)) (congrArg (·.left) h1))
    choose v h1 h2 using hσ'
    refine ⟨B, inferInstance, b, j, j', v, hj, hjb, hj'b, h1, fun t => tors_ext h ?_ ?_, fun t => tors_ext h ?_ ?_⟩
    · rw [Category.assoc, h1, Over.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjb]; rfl
    · rw [Category.assoc, h2, hσj]
    · rw [Category.assoc, Category.assoc, h1, hF1, ← Category.assoc, Over.w, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hj'b, CommRingCat.ofHom_comp, Spec.map_comp]; rfl
    · rw [Category.assoc, Category.assoc, h2, hF2, hσj']

end PositivityTheory.HtPt.Htat
end
end

