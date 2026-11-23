module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

section Ring

variable {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] [LinearOrder n]

private theorem diag_mul {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ borel R n) (i : n) :
    ((a * b : GL n R) : Matrix n n R) i i = (a : Matrix n n R) i i * (b : Matrix n n R) i i := by
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [(mem_borel R).mp ha i k h, zero_mul]
  · rw [(mem_borel R).mp hb k i h, mul_zero]

private theorem diag_inv {a : GL n R} (ha : a ∈ borel R n) (i : n) :
    (a : Matrix n n R) i i * ((a⁻¹ : GL n R) : Matrix n n R) i i = 1 := by
  rw [← diag_mul ha (inv_mem ha), mul_inv_cancel, Units.val_one, one_apply_eq]

variable (n) in
private def BC (C : Subgroup Rˣ) : Subgroup (GL n R) where
  carrier := {g | g ∈ borel R n ∧ ∀ i, ∃ c ∈ C, (c : R) = (g : Matrix n n R) i i}
  one_mem' := ⟨one_mem _, fun i => ⟨1, one_mem _, by simp⟩⟩
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, fun i => by
    obtain ⟨c, hc, e⟩ := ha.2 i
    obtain ⟨d, hd, e'⟩ := hb.2 i
    exact ⟨c * d, mul_mem hc hd, by rw [diag_mul ha.1 hb.1, Units.val_mul, e, e']⟩⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, fun i => by
    obtain ⟨c, hc, e⟩ := ha.2 i
    refine ⟨c⁻¹, inv_mem hc, ?_⟩
    have := diag_inv ha.1 i
    rw [← e] at this
    exact Units.inv_eq_of_mul_eq_one_right this⟩

private theorem BC_conj {C : Subgroup Rˣ} {a b : GL n R} (ha : a ∈ borel R n) (hb : b ∈ BC n C) :
    a * b * a⁻¹ ∈ BC n C := by
  refine ⟨mul_mem (mul_mem ha hb.1) (inv_mem ha), fun i => ?_⟩
  obtain ⟨c, hc, e⟩ := hb.2 i
  refine ⟨c, hc, ?_⟩
  rw [diag_mul (mul_mem ha hb.1) (inv_mem ha), diag_mul ha hb.1, ← e, mul_right_comm,
    diag_inv ha i, one_mul]

private theorem BC_top : BC n (⊤ : Subgroup Rˣ) = borel R n := by
  ext g
  refine ⟨fun h => h.1, fun h => ⟨h, fun i => ?_⟩⟩
  exact ⟨Units.mkOfMulEqOne _ _ (diag_inv h i), trivial, rfl⟩

private theorem map_diagT {S : Type} [CommRing S] (f : R →+* S) (d : n → Rˣ) :
    GeneralLinearGroup.map (n := n) f (diagT R n d) = diagT S n fun i => Units.map f.toMonoidHom (d i) := by
  ext i j
  change f (((diagT R n d : GL n R) : Matrix n n R) i j) = _
  rw [val_diagT, val_diagT]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ hij]

private theorem map_borel {S : Type} [CommRing S] (f : R →+* S) {g : GL n R} (hg : g ∈ borel R n) :
    GeneralLinearGroup.map (n := n) f g ∈ borel S n := by
  refine (mem_borel S).2 fun i j hij => ?_
  show f ((g : Matrix n n R) i j) = 0
  rw [(mem_borel R).1 hg i j hij, map_zero]

private theorem map_unipB {S : Type} [CommRing S] (f : R →+* S) {g : GL n R} (hg : g ∈ unipB R n) :
    GeneralLinearGroup.map (n := n) f g ∈ unipB S n := by
  have h := (mem_unipB R).1 hg
  refine (mem_unipB S).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [h.1 i j hij, map_zero]
  · show f ((g : Matrix n n R) i i) = 1
    rw [h.2 i, map_one]

private theorem factor [IsLocalRing R] (C : Subgroup (IsLocalRing.ResidueField R)ˣ) (h : GL n R)
    (hh : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h ∈ BC n C) :
    ∃ d : n → Rˣ, (∀ i, Units.map (IsLocalRing.residue R).toMonoidHom (d i) ∈ C) ∧ ∃ u ∈ unipB R n,
      ∃ L ∈ (GeneralLinearGroup.map (n := n) (IsLocalRing.residue R)).ker, h = diagT R n d * u * L := by
  obtain ⟨L, hL1, hL2, hL3⟩ := IwahoriOnto.exists_mul_mem_borel h hh.1
  obtain ⟨u, hu, hp⟩ := exists_levi_mul_unip R (points n) ⟨h * L, hL3⟩
  set d : n → Rˣ := (leviTorus R n).symm (leviProj R (points n) ⟨h * L, hL3⟩) with hd_def
  have hd : diagT R n d = leviEmb R (points n) (leviProj R (points n) ⟨h * L, hL3⟩) := by
    change leviEmb R (points n) ((leviTorus R n) ((leviTorus R n).symm _)) = _
    rw [MulEquiv.apply_symm_apply]
  have hp' : h * L = diagT R n d * u := by
    rw [hd]
    exact hp
  have heq : h = diagT R n d * u * L⁻¹ := by rw [← hp', mul_inv_cancel_right]
  have hLb : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L ∈
      borel (IsLocalRing.ResidueField R) n := by
    have e : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L =
        (GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h)⁻¹ *
          GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) (h * L) := by
      rw [map_mul, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hh.1) (map_borel _ hL3)
  have hred : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) L = 1 := by
    ext i j
    rw [Units.val_one]
    rcases lt_trichotomy i j with hij | hij | hij
    · change IsLocalRing.residue R ((L : Matrix n n R) i j) = _
      rw [hL1 i j hij, map_zero, Matrix.one_apply_ne (ne_of_lt hij)]
    · subst hij
      change IsLocalRing.residue R ((L : Matrix n n R) i i) = _
      rw [hL2 i, map_one, Matrix.one_apply_eq]
    · rw [(mem_borel _).mp hLb i j hij, Matrix.one_apply_ne (ne_of_gt hij)]
  have hdb : diagT R n d ∈ borel R n := (mem_borel R).mpr fun i j hij => by
    rw [val_diagT, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
  have hub : u ∈ borel R n := (mem_borel R).mpr ((mem_unipB R).mp hu).1
  have hrh : GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) h =
      GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) (diagT R n d) *
        GeneralLinearGroup.map (n := n) (IsLocalRing.residue R) u := by
    rw [heq, map_mul, map_mul, map_inv, hred, inv_one, mul_one]
  refine ⟨d, fun i => ?_, u, hu, L⁻¹, inv_mem hred, heq⟩
  obtain ⟨c, hc, e⟩ := hh.2 i
  rw [hrh, diag_mul (map_borel _ hdb) (map_borel _ hub)] at e
  have h1 := ((mem_unipB _).mp (map_unipB (IsLocalRing.residue R) hu)).2 i
  rw [h1, mul_one, map_diagT, val_diagT, Matrix.diagonal_apply_eq] at e
  have hc' : c = Units.map (IsLocalRing.residue R).toMonoidHom (d i) := Units.ext e
  rw [← hc']
  exact hc

end Ring

section Loc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

private theorem iwC_eq (C : Subgroup 𝓀[k]ˣ) :
    iwC k n C = ((BC (Fin n) C).comap (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]))).map
      (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · refine Subgroup.map_mono fun g hg => ?_
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
      exact one_mem _
    · rintro _ ⟨hu, h, rfl⟩
      have h1 := (mem_unipB k).1 hu
      have h2 : h ∈ unipB 𝒪[k] (Fin n) := (mem_unipB _).2
        ⟨fun i j hij => hinj ((h1.1 i j hij).trans (map_zero _).symm),
          fun i => hinj ((h1.2 i).trans (map_one _).symm)⟩
      have h3 := (mem_unipB _).1 (map_unipB (IsLocalRing.residue 𝒪[k]) h2)
      exact ⟨h, ⟨(mem_borel _).2 h3.1, fun i => ⟨1, one_mem _, (h3.2 i).symm⟩⟩, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have h1 : ∀ i, ∃ d : 𝒪[k]ˣ, Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom d ∈ C ∧
          Units.map (algebraMap 𝒪[k] k).toMonoidHom d = t i := fun i => ht i trivial
      choose d hd e using h1
      refine ⟨diagT _ _ d, ?_, by rw [map_diagT, funext e]⟩
      show GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) _ ∈ BC (Fin n) C
      rw [map_diagT]
      refine ⟨(mem_borel _).2 fun i j hij => ?_, fun i => ⟨_, hd i, ?_⟩⟩
      · rw [val_diagT, diagonal_apply_ne _ hij.ne']
      · rw [val_diagT, diagonal_apply_eq]
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨d, hd, u, hu, L, hL, rfl⟩ := factor C h hh
    rw [map_mul, map_mul]
    refine mul_mem (mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨L, hL, rfl⟩))
    · rw [map_diagT]
      exact ⟨_, fun i _ => ⟨d i, hd i, rfl⟩, rfl⟩
    · exact ⟨map_unipB _ hu, u, rfl⟩

end Loc

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.memIwC :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), (∀ g : GL (Fin n) k, g ∈ iwC k n C ↔ g ∈ iwahori k (Fin n) ∧ ∀ i, ∃ c ∈ unitsC k C, (c : k) = (g : Matrix (Fin n) (Fin n) k) i i) ∧ iwC k n ⊤ = iwahori k (Fin n) ∧ (∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwC k n C, a * b * a⁻¹ ∈ iwC k n C) ∧ ∀ x : kˣ, x ∈ unitsC k ⊤ ↔ valuation k (x : k) = 1 := by
  intro k _ _ _ _ n C
  refine ⟨fun g => ?_, ?_, ?_, fun x => ?_⟩
  · rw [iwC_eq]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨h, hh.1, rfl⟩, fun i => ?_⟩
      obtain ⟨c, hc, e⟩ := hh.2 i
      have hu : IsUnit ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i) := by
        apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
        intro h0
        apply c.ne_zero
        rw [e]
        exact h0
      have hcu : Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom hu.unit = c := by
        apply Units.ext
        rw [e]
        rfl
      refine ⟨Units.map (algebraMap 𝒪[k] k).toMonoidHom hu.unit, ⟨hu.unit, ?_, rfl⟩, rfl⟩
      show Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom hu.unit ∈ C
      rw [hcu]
      exact hc
    · rintro ⟨⟨h, hh, rfl⟩, hd⟩
      refine ⟨h, ⟨hh, fun i => ?_⟩, rfl⟩
      obtain ⟨c, ⟨c', hc', rfl⟩, e⟩ := hd i
      have hce : (c' : 𝒪[k]) = (h : Matrix (Fin n) (Fin n) 𝒪[k]) i i := Subtype.ext e
      refine ⟨Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom c', hc', ?_⟩
      change IsLocalRing.residue 𝒪[k] (c' : 𝒪[k]) =
        IsLocalRing.residue 𝒪[k] ((h : Matrix (Fin n) (Fin n) 𝒪[k]) i i)
      rw [hce]
  · rw [iwC_eq, BC_top]
    rfl
  · intro a ha b hb
    rw [iwC_eq] at hb ⊢
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨a' * b' * a'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact BC_conj ha' hb'
  · constructor
    · rintro ⟨u, -, rfl⟩
      exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).mp u.isUnit
    · intro hx
      let xo : 𝒪[k] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
      have hu : IsUnit xo :=
        (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).mpr hx
      exact ⟨hu.unit, Subgroup.mem_top _, Units.ext rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMonoidExt
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.monoidExt :
    ∀ (T H : Type) [CommGroup T] [Monoid H] (P : Submonoid T) (f : T → H), (∀ t : T, ∃ a ∈ P, ∃ b ∈ P, t = a * b⁻¹) → f 1 = 1 → (∀ a ∈ P, ∀ b ∈ P, f (a * b) = f a * f b) → (∀ a ∈ P, IsUnit (f a)) → ∃! θ : T →* Hˣ, ∀ a ∈ P, (θ a : H) = f a := by
  intro T H _ _ P f hgen h1 hmul hunit
  classical
  let U : T → Hˣ := fun a => if h : a ∈ P then (hunit a h).unit else 1
  have hU : ∀ a ∈ P, (U a : H) = f a := by
    intro a ha
    simp [U, ha]
  have hUmul : ∀ a ∈ P, ∀ b ∈ P, U (a * b) = U a * U b := by
    intro a ha b hb
    ext
    rw [Units.val_mul, hU _ (P.mul_mem ha hb), hU a ha, hU b hb, hmul a ha b hb]
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, Commute (U a) (U b) := by
    intro a ha b hb
    show U a * U b = U b * U a
    rw [← hUmul a ha b hb, ← hUmul b hb a ha, mul_comm a b]
  have hU1 : U 1 = 1 := Units.ext (by rw [hU 1 P.one_mem, h1]; rfl)
  have hwd : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P, a * b⁻¹ = c * d⁻¹ →
      U a * (U b)⁻¹ = U c * (U d)⁻¹ := by
    intro a ha b hb c hc d hd h
    have h' : a * d = c * b := by
      calc a * d = (a * b⁻¹) * (b * d) := by rw [mul_assoc, inv_mul_cancel_left]
        _ = (c * d⁻¹) * (b * d) := by rw [h]
        _ = c * b := by rw [mul_comm b d, mul_assoc, inv_mul_cancel_left]
    have hU' : U a * U d = U c * U b := by
      rw [← hUmul a ha d hd, ← hUmul c hc b hb, h']
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, (hcomm d hd b hb).inv_left.eq, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, hU']
  choose A hA B hB hAB using hgen
  let θ : T →* Hˣ :=
    { toFun := fun t => U (A t) * (U (B t))⁻¹
      map_one' := by
        show U (A 1) * (U (B 1))⁻¹ = 1
        rw [hwd (A 1) (hA 1) (B 1) (hB 1) 1 P.one_mem 1 P.one_mem (by rw [← hAB 1]; simp), hU1]
        simp
      map_mul' := fun t s => by
        show U (A (t * s)) * (U (B (t * s)))⁻¹ = U (A t) * (U (B t))⁻¹ * (U (A s) * (U (B s))⁻¹)
        have he : A (t * s) * (B (t * s))⁻¹ = (A t * A s) * (B t * B s)⁻¹ := by
          rw [← hAB (t * s)]
          calc t * s = A t * (B t)⁻¹ * (A s * (B s)⁻¹) := by rw [← hAB t, ← hAB s]
            _ = A t * A s * (B t * B s)⁻¹ := by
              rw [_root_.mul_inv_rev]
              ac_rfl
        rw [hwd _ (hA _) _ (hB _) _ (P.mul_mem (hA t) (hA s)) _ (P.mul_mem (hB t) (hB s)) he,
          hUmul _ (hA t) _ (hA s), hUmul _ (hB t) _ (hB s), _root_.mul_inv_rev]
        have c1 : Commute (U (B t))⁻¹ (U (A s)) := (hcomm _ (hB t) _ (hA s)).inv_left
        have c2 : Commute (U (B t))⁻¹ (U (B s))⁻¹ := (hcomm _ (hB t) _ (hB s)).inv_inv
        simp only [mul_assoc]
        rw [← mul_assoc (U (B t))⁻¹, c1.eq, mul_assoc, c2.eq] }
  have hθ : ∀ a ∈ P, (θ a : H) = f a := by
    intro a ha
    show ((U (A a) * (U (B a))⁻¹ : Hˣ) : H) = f a
    rw [hwd (A a) (hA a) (B a) (hB a) a ha 1 P.one_mem (by rw [← hAB a]; simp), hU1, inv_one,
      mul_one, hU a ha]
  refine ⟨θ, hθ, fun θ' h' => ?_⟩
  have agree : ∀ a ∈ P, θ' a = θ a := fun a ha => Units.ext ((h' a ha).trans (hθ a ha).symm)
  apply MonoidHom.ext
  intro t
  rw [hAB t, map_mul, map_mul, map_inv, map_inv, agree _ (hA t), agree _ (hB t)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaTie
section
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.evaluation_unit_factor {A H E : Type} [CommRing A] [Semiring H] [Algebra A H] [Semiring E] [Algebra A E]
    (ev : H →ₐ[A] E) (a y z : H) (c : A) (u v w : Eˣ) (h : a * y = c • z) (hy : ev y = v) (hz : ev z = w)
    (hw : w = u * v) : ev a = c • (u : E) := by
  have h' := congrArg ev h
  rw [map_mul, map_smul, hy, hz, hw, Units.val_mul, ← smul_mul_assoc] at h'
  exact (Units.mul_left_inj _).1 h'

theorem UpperTheory.V.AlgebraTools.thetaTie :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ (b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤))) (ev : HkAlg A (iwC k n ⊤) →ₐ[A] Module.End A (fixd ρ (iwC k n ⊤))) (θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n ⊤)))ˣ), (∀ g, ev (hT A (iwC k n ⊤) g) = hk ρ (iwC k n ⊤) g) → (∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (diagT k (Fin n) t)) → (∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) → ∀ i : Fin n, ev (b.th (MvPolynomial.X i)) = ((resCard k : A) ^ (i : ℕ)) • (θ (Pi.mulSingle i x) : Module.End A (fixd ρ (iwC k n ⊤))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx _ b ev θ hev hθ hb i
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  have hdom : ∀ m : ℕ, Dom (fun j : Fin n => x ^ fund n m j) := by
    intro m j l hjl
    have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
    simp only [fund]
    by_cases h1 : (l : ℕ) < m
    · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
      simp [h1, h2]
    · by_cases h2 : (j : ℕ) < m
      · simpa [h1, h2] using hx1
      · simp [h1, h2]
  have hsplit : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
      = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
    funext j
    simp only [fund, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
      rw [Pi.mulSingle_eq_of_ne hj, one_mul]
      by_cases h : (j : ℕ) < (i : ℕ)
      · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
      · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
  refine UpperTheory.V.AlgebraTools.evaluation_unit_factor ev _ _ _ _ _ (θ fun j : Fin n => x ^ fund n (i : ℕ) j)
    (θ fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j) (hb i) ?_ ?_ ?_
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · rw [hsplit]
    exact map_mul θ _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegLim
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.qRegAt_uLim :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (y : σ → R) (a k : ℕ), Antitone I → a < k →
      (∀ j, ∀ᶠ N in F, QRegAt (M N) y (I j) a) →
      QRegAt (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ I j) M) y ⊥ a := by
  intro R σ _ _ F hF I M _ _ y a k hI hak hq
  classical
  set Y : Ideal R := Ideal.span (Set.range y) with hY
  have hYfg : Y.FG := ⟨(Set.finite_range y).toFinset, by simp [hY]⟩
  have hK : Antitone (fun j ↦ Y ^ k ⊔ I j) := fun i j hij ↦ sup_le_sup_left (hI hij) _
  have hk1 : Y ^ k ≤ Y ^ (a + 1) := Ideal.pow_le_pow_right (by omega)
  intro c hc
  choose p hp using fun α ↦ ULim.mk_surjective F (fun j ↦ Y ^ k ⊔ I j) M (c α)
  have hsum : ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • c α =
      ULim.mk F (fun j ↦ Y ^ k ⊔ I j) M
        (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) := by
    have e : (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) =
        ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α := by
      ext N
      simp [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp [hp]
  rw [sup_bot_eq, hsum, ULim.mem_smul_top_iff R F hF _ M (Y ^ (a + 1)) hYfg.pow hK] at hc
  intro α
  rw [sup_bot_eq, ← hp α, ULim.mem_smul_top_iff R F hF _ M Y hYfg hK]
  intro j
  filter_upwards [hc j, hq j] with N hN hqN
  have hN' : ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑β • p β N ∈
      (Y ^ (a + 1) ⊔ I j) • (⊤ : Submodule R (M N)) :=
    Submodule.smul_mono_left (sup_le le_sup_left (sup_le (hk1.trans le_sup_left) le_sup_right)) hN
  exact Submodule.smul_mono_left (sup_le_sup_left le_sup_right Y) (hqN (fun β ↦ p β N) hN' α)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilMapMem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem topNil_map_mem {R M M' κ : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (T : κ → Module.End R M)
    (T' : κ → Module.End R M') (f : M →ₗ[R] M') (hf : ∀ i x, f (T i x) = T' i (f x))
    {x : M} (hx : x ∈ topNil I T) : f x ∈ topNil I T' := by
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) x ∈ (I ^ j • ⊤ : Submodule R M) at hx
  change ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T' i ^ r) (f x) ∈ (I ^ j • ⊤ : Submodule R M')
  intro i j
  have hpow : ∀ r : ℕ, f ((T i ^ r) x) = (T' i ^ r) (f x) := by
    intro r
    induction r with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hf, ih]
  have hle : Submodule.map f (I ^ j • (⊤ : Submodule R M)) ≤ I ^ j • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  filter_upwards [hx i j] with r hr
  rw [← hpow]
  exact hle ⟨_, hr, rfl⟩

theorem UpperTheory.V.AlgebraTools.topNil_map :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] (M' : Type) [AddCommGroup M'] [Module R M'] [Module.Finite R M] [Module.Finite R M'] (T : κ → Module.End R M) (T' : κ → Module.End R M'),
      (∀ i j, Commute (T i) (T j)) → (∀ i j, Commute (T' i) (T' j)) → ∀ f : M →ₗ[R] M', (∀ i x, f (T i x) = T' i (f x)) →
      (topNil (IsLocalRing.maximalIdeal R) T).map f = topNil (IsLocalRing.maximalIdeal R) T' ⊓ LinearMap.range f ∧
      ∀ I : Ideal R, LinearMap.ker f = I • ⊤ → LinearMap.ker f ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ M' _ _ _ _ T T' hT hT' f hf
  have hsmul := (topNil_free R κ M T hT).2.1
  refine ⟨le_antisymm ?_ ?_, fun I hI => by rw [hI]; exact hsmul I⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact ⟨topNil_map_mem _ T T' f hf hx, x, rfl⟩
  · rintro y ⟨hy, x, rfl⟩
    have hTx : ∀ i j x, T i (T j x) = T j (T i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT i j).eq, Module.End.mul_apply]
    have hT'x : ∀ i j x, T' i (T' j x) = T' j (T' i x) := fun i j x => by
      rw [← Module.End.mul_apply, (hT' i j).eq, Module.End.mul_apply]
    let S : κ → Module.End R (M × M') := fun i => (T i).prodMap (T' i)
    have hS : ∀ i j, Commute (S i) (S j) := by
      intro i j
      show S i * S j = S j * S i
      apply LinearMap.ext
      intro p
      simp [S, Module.End.mul_apply, hTx i j, hT'x i j]
    obtain ⟨⟨C, hC, hstab⟩, -⟩ := topNil_free R κ (M × M') S hS
    let φ : Module.End R (M × M') := (LinearMap.inr R M M').comp (f.comp (LinearMap.fst R M M'))
    have hφ : ∀ i, Commute φ (S i) := by
      intro i
      show φ * S i = S i * φ
      apply LinearMap.ext
      intro p
      simp [φ, S, Module.End.mul_apply, hf]
    have hmem : ((x, 0) : M × M') ∈ topNil (IsLocalRing.maximalIdeal R) S ⊔ C := by
      rw [hC.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn, c, hc, hnc⟩ := Submodule.mem_sup.mp hmem
    have hn1 : n.1 ∈ topNil (IsLocalRing.maximalIdeal R) T :=
      topNil_map_mem _ S T (LinearMap.fst R M M') (fun i p => rfl) hn
    have hφc : φ c ∈ C := (hstab φ hφ).2 c hc
    have hx : x = n.1 + c.1 := by
      have := congrArg Prod.fst hnc
      simpa using this.symm
    have hfc : f c.1 ∈ topNil (IsLocalRing.maximalIdeal R) T' := by
      have : f c.1 = f x - f n.1 := by
        rw [hx]
        simp
      rw [this]
      exact Submodule.sub_mem _ hy (topNil_map_mem _ T T' f hf hn1)
    have hφn : φ c ∈ topNil (IsLocalRing.maximalIdeal R) S := by
      have := topNil_map_mem _ T' S (LinearMap.inr R M M') (fun i y => by simp [S]) hfc
      simpa [φ] using this
    have h0 : φ c = 0 := (Submodule.disjoint_def.mp hC.disjoint) _ hφn hφc
    have hfc0 : f c.1 = 0 := by
      have := congrArg Prod.snd h0
      simpa [φ] using this
    refine ⟨n.1, hn1, ?_⟩
    rw [hx, map_add (f := _), hfc0, add_zero]
end

