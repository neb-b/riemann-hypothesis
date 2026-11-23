module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum


open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in
theorem lin_of_isEmpty {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} [hT : IsEmpty T'.left]
    (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Lin G L N h b c s := by
  intro z
  exact isEmptyElim ((fst T' G).left z)

theorem isEmpty_of_eq_bot {Z : Scheme.{0}} {U : Z.Opens} (h : U = ⊥) : IsEmpty U.toScheme := by
  subst h
  exact ⟨fun x => by simpa using x.2⟩

theorem subsingleton_sections_of_isEmpty {X : Scheme.{0}} [IsEmpty X] : Subsingleton Γ(X, ⊤) := by
  refine CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)
  ext x
  exact isEmptyElim x


open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in
theorem trans_of_inf_eq_bot {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {n : ℕ} (r s : ℤ) {U V : Z.Opens}
    (hUV : U ⊓ V = ⊥) (thU : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk U.ι)))
    (thV : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk V.ι)))
    (bU : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) (bV : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk V.ι)))
    (g : Γ(Z, U ⊓ V)) :
    ∃ (c : Γ((U ⊓ V).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((U ⊓ V).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => thU) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        (fun _ : Fin 1 => thV) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => bU k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        bV (fun k' => M.val k k') t) ∧
    (U ⊓ V).topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val := by
  have hE : IsEmpty (U ⊓ V).toScheme := isEmpty_of_eq_bot hUV
  have := subsingleton_sections_of_isEmpty (X := (U ⊓ V).toScheme)
  have sec : ∀ M : ℕ, LB.Sec (LPow G L (M : ℤ) (Over.mk (U ⊓ V).ι)) := fun M =>
    { f := fun _ => 0
      compat := fun _ _ => fn_ext fun y _ => (hE.false ((fst (Over.mk (U ⊓ V).ι) G).left y)).elim }
  refine ⟨1, 1, ⟨sec 1, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _⟩,
    fun k => ⟨sec N, lin_of_isEmpty (hT := hE) G L N _ _ _ _, lin_of_isEmpty (hT := hE) G L N _ _ _ _⟩,
    Subsingleton.elim _ _⟩

theorem hasFrames_sumLB : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  intro Z G L N A B n r s hAB hA hB
  obtain ⟨thA, bA, hAt, hAb⟩ := hA
  obtain ⟨thB, bB, hBt, hBb⟩ := hB
  refine ⟨fun | .inl i => thA i | .inr j => thB j, fun | .inl i => bA i | .inr j => bB j, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · exact hAt i j
    · exact trans_of_inf_eq_bot G L N r s (hAB i j) (thA i) (thB j) (bA i) (bB j) _
    · exact trans_of_inf_eq_bot G L N r s (by rw [inf_comm]; exact hAB j i) (thB i) (thA j) (bB i) (bA j) _
    · exact hBt i j
  · rintro (i | i) W _ _ _ hW χ hχ
    · exact hAb i W hW χ hχ
    · exact hBb i W hW χ hχ

end GlobalTheory.ModelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

def noTraitZero {X : Scheme.{0}} (M : LB X) : M.Sec := ⟨fun _ => 0, by simp⟩

theorem noTrait_gs_zero {Y X : Scheme.{0}} (r : Y ⟶ X) (y : Y) (U : X.Opens) : gs r y U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

theorem lin_noTraitZero {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (c : Fin n → Γ(T'.left, ⊤)) : GlobalTheory.LN.Lin G L N h (fun _ => noTraitZero _) c (noTraitZero _) := by
  intro z J _
  refine (noTrait_gs_zero _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (congrArg _ (noTrait_gs_zero _ _ _)).trans (mul_zero _)

theorem noTrait_exists_gl_det_eq {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    ∃ M : GL (Fin n) R, Matrix.GeneralLinearGroup.det M = u := by
  have hd : (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) ⟨0, hn⟩ u.val)).det = u.val := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hd]; exact u.isUnit), Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hd

theorem hasFrames_rank_of_isEmpty (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ)
    (hn : 1 ≤ n') (hZ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z))
    (h : HasFrames G L N A n r s) : HasFrames G L N A n' r s := by
  obtain ⟨th, b, h₁, -⟩ := h
  refine ⟨th, fun _ _ => noTraitZero _, fun i j => ?_, fun i W _ _ _ hW χ _ => ((hZ W hW).false (χ ≫ (A.U i).ι)).elim⟩
  obtain ⟨c, M, h₂, -, h₃⟩ := h₁ i j
  obtain ⟨M', hM⟩ := noTrait_exists_gl_det_eq hn (Matrix.GeneralLinearGroup.det M)
  exact ⟨c, M', h₂, fun k => ⟨noTraitZero _, lin_noTraitZero G L N _ _, lin_noTraitZero G L N _ _⟩, by rw [hM]; exact h₃⟩

end GlobalTheory.ModelSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocalizationOfLeClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.JoinRing

def coprimeNat (p : ℕ) (A : Type) [CommRing A] : Submonoid A where
  carrier := {x | ∃ m : ℕ, m.Coprime p ∧ x = m}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, Nat.Coprime.mul_left ha hb, by simp⟩

theorem ne_zero_of_coprime {p m : ℕ} (hp : p.Prime) (hm : m.Coprime p) : m ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hm)

theorem coprimeNat_le {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] [IsDomain A] [CharZero A] :
    coprimeNat p A ≤ nonZeroDivisors A := by
  rintro _ ⟨m, hm, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm))

theorem isLocalization_of_le_closure {p : ℕ} (hp : p.Prime) (A : Type) [CommRing A] (T : Subring ℂ) [Algebra A T]
    (hinj : Function.Injective (algebraMap A T)) (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsLocalization (coprimeNat p A) T := by
  have h0 : ∀ m : ℕ, m.Coprime p → (m : ℂ) ≠ 0 := fun m hm => Nat.cast_ne_zero.mpr (ne_zero_of_coprime hp hm)
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : ℂ)} ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹}),
      ∃ m : ℕ, m.Coprime p ∧ ∃ a, z * m = (algebraMap A T a : ℂ) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | ⟨m, hm, rfl⟩
      · exact ⟨1, by simp, a, by simp⟩
      · exact ⟨m, hm, 1, by simp [h0 m hm]⟩
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | one => exact ⟨1, by simp, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * k + b * m, ?_⟩
      simp only [map_add (f := _), map_mul, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, hm, a, ha⟩ := hx
      refine ⟨m, hm, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, a, ha⟩ := hx
      obtain ⟨k, hk, b, hb⟩ := hy
      refine ⟨m * k, Nat.Coprime.mul_left hm hk, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    simp only [map_natCast]
    refine IsUnit.of_mul_eq_one ⟨_, hinv m hm⟩ (Subtype.ext ?_)
    simp [h0 m hm]
  · intro z
    obtain ⟨m, hm, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨m, m, hm, rfl⟩), Subtype.ext ?_⟩
    simp only [map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem inv_mem_ZP {p m : ℕ} (k : ℕ) (hm : m.Coprime p) : (m : ℂ)⁻¹ ∈ ZP p k :=
  Subring.subset_closure (Or.inr ⟨m, hm, rfl⟩)


open CycBase in
theorem isDedekindDomain_ZP {n p : ℕ} (e : ℕ) (hn : n.Prime) (hp : p.Prime) : IsDedekindDomain (ZP p (n ^ e)) := by
  open GlobalTheory.ZM.CycBase in
  haveI := Fact.mk hn
  have hk : n ^ e ≠ 0 := NeZero.ne _
  haveI : IsCyclotomicExtension {n ^ e} ℚ (CF (n ^ e)) := cyc
  haveI : NumberField (CF (n ^ e)) := IsCyclotomicExtension.numberField {n ^ e} ℚ _
  let io : 𝓞 (CF (n ^ e)) →+* ℂ := (CF (n ^ e)).val.toRingHom.comp (algebraMap _ (CF (n ^ e)))
  have hio : Function.Injective io :=
    Subtype.val_injective.comp (RingOfIntegers.coe_injective (K := CF (n ^ e)))
  letI : Algebra (𝓞 (CF (n ^ e))) (ZP p (n ^ e)) := (io.codRestrict _ (mem_ZP p n e hn)).toAlgebra
  have : IsLocalization (coprimeNat p (𝓞 (CF (n ^ e)))) (ZP p (n ^ e)) := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => hio (congrArg (fun z : ZP p (n ^ e) => (z : ℂ)) h))
      (fun m hm => inv_mem_ZP _ hm) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨(zF_prim hk).toInteger, rfl⟩
    · exact Or.inr h
  exact IsLocalization.isDedekindDomain _ (coprimeNat_le hp (𝓞 (CF (n ^ e)))) _

theorem isDedekindDomain_RZ_of_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {S A e : ℕ}
    (hS : 0 < S) (hA : 0 < A) (h : A ∣ S ^ e) : IsDedekindDomain (RZ H S A) := by
  obtain ⟨l, rfl⟩ : ∃ l : Level H, l.A = A := ⟨GlobalTheory.HostModel.level H A hA, rfl⟩
  exact GlobalTheory.BaseRing.isDedekindDomain_RZ l hS h

theorem flat_inclusion {S T : Subring ℂ} (h : S ≤ T) [IsDedekindDomain S] : Flat (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have htf : Module.IsTorsionFree S T := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat S T))

theorem noetherian_preimmersion {p : ℕ} (hp : p.Prime) {S T : Subring ℂ} (h : S ≤ T) [IsNoetherianRing S]
    (hinv : ∀ m : ℕ, m.Coprime p → (m : ℂ)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ((S : Set ℂ) ∪ {x | ∃ n : ℕ, n.Coprime p ∧ x = (n : ℂ)⁻¹})) :
    IsNoetherianRing T ∧ IsPreimmersion (spMap (Subring.inclusion h)) := by
  letI : Algebra S T := (Subring.inclusion h).toAlgebra
  have hL : IsLocalization (coprimeNat p S) T := by
    refine isLocalization_of_le_closure hp _ _ (fun x y h => Subtype.ext (congrArg (fun z : T => (z : ℂ)) h))
      hinv (hT.trans (Subring.closure_mono ?_))
    rintro x (hx | hx)
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr hx
  exact ⟨IsLocalization.isNoetherianRing (coprimeNat p S) _ inferInstance,
    IsPreimmersion.of_isLocalization (R := S) (S := T) (coprimeNat p S)⟩

theorem join_rings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n N p : ℕ), n.Prime → (∃ j, 1 ≤ j ∧ N = n ^ j) → p.Prime → p ≠ n → IsDedekindDomain (RZ H n N) ∧ IsNoetherianRing ↥(RZ H n N ⊔ ZP p N) ∧ Flat (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ IsPreimmersion (spMap (Subring.inclusion (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N))) ∧ Flat (spMap (Subring.inclusion (le_sup_right : ZP p N ≤ RZ H n N ⊔ ZP p N))) := by
  rintro E _ _ _ H n N p hn ⟨j, -, hN⟩ hp -
  have hD : IsDedekindDomain (RZ H n N) :=
    isDedekindDomain_RZ_of_dvd H (e := j) hn.pos (hN ▸ pow_pos hn.pos j) (hN ▸ dvd_rfl)
  have hZ : IsDedekindDomain (ZP p N) := hN ▸ isDedekindDomain_ZP j hn hp
  have h := noetherian_preimmersion hp (le_sup_left : RZ H n N ≤ RZ H n N ⊔ ZP p N)
    (fun m hm => (le_sup_right : ZP p N ≤ _) (inv_mem_ZP _ hm))
    (sup_le (fun x hx => Subring.subset_closure (Or.inl hx)) (Subring.closure_mono (by
      rintro x (rfl | h)
      · exact Or.inl (RZ.ze H n N).2
      · exact Or.inr h)))
  exact ⟨hD, h.1, flat_inclusion _, h.2, flat_inclusion _⟩

end GlobalTheory.JoinRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion {A : Type} [CommRing A]
    {B X : Scheme.{0}} (e : B ⟶ X)
    [IsImmersion e] {x : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A} (hx : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver x) [IsProper (e ≫ x)] :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (e ≫ x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at hx
  obtain ⟨N, i, hi, -, rfl⟩ := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver
  haveI : IsProper (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str A N
  haveI : IsProper ((e ≫ i) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (e ≫ i) := IsProper.of_comp (e ≫ i) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N)
  exact ⟨N, e ≫ i, .of_isPreimmersion _ (e ≫ i).isClosedMap.isClosed_range, by simp⟩

open AlgebraicGeometry CategoryTheory Limits in
private theorem isPullback_fst_comp_map {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ Z)
    (t : W ⟶ Z) :
    IsPullback (pullback.fst (f ≫ s) t)
      (pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp)) f (pullback.fst s t) := by
  have h₁ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst s t =
      pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have h₂ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd s t =
      pullback.snd (f ≫ s) t := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_bot ?_ h₁.symm (IsPullback.of_hasPullback s t)
  rw [h₂]
  exact IsPullback.of_hasPullback (f ≫ s) t

open AlgebraicGeometry CategoryTheory Limits in
private theorem isImmersion_pullback_lift_of_isPullback {X Y Z W P : Scheme.{0}} (f : X ⟶ Y)
    (s : Y ⟶ Z) (t : W ⟶ Z) (y : W ⟶ Y) (hy : y ≫ s = t) (φ : P ⟶ X) (b : P ⟶ W)
    (h : IsPullback φ b f y) :
    IsImmersion (pullback.lift (f := f ≫ s) (g := t) φ b
      (by rw [← hy, ← Category.assoc, h.w, Category.assoc])) := by
  set Γ : W ⟶ pullback s t := pullback.lift y (𝟙 W) (by rw [hy, Category.id_comp]) with hΓdef
  have hΓs : Γ ≫ pullback.snd s t = 𝟙 W := pullback.lift_snd _ _ _
  have hΓf : Γ ≫ pullback.fst s t = y := pullback.lift_fst _ _ _
  haveI : IsImmersion (Γ ≫ pullback.snd s t) := by rw [hΓs]; infer_instance
  haveI : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd s t)
  set e : P ⟶ pullback (f ≫ s) t := pullback.lift (f := f ≫ s) (g := t) φ b
    (by rw [← hy, ← Category.assoc, h.w, Category.assoc]) with hedef
  have hef : e ≫ pullback.fst (f ≫ s) t = φ := pullback.lift_fst _ _ _
  have hes : e ≫ pullback.snd (f ≫ s) t = b := pullback.lift_snd _ _ _
  set g := pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) with hgdef
  have hg₁ : g ≫ pullback.fst s t = pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd s t = pullback.snd (f ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : e ≫ g = b ≫ Γ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hg₁, hΓf, ← Category.assoc, hef, h.w]
    · rw [Category.assoc, Category.assoc, hg₂, hΓs, hes, Category.comp_id]
  have hleft : IsPullback e b g Γ := by
    refine IsPullback.of_right ?_ hsq (isPullback_fst_comp_map f s t)
    rw [hef, hΓf]
    exact h
  exact MorphismProperty.of_isPullback (P := @IsImmersion) hleft.flip ‹IsImmersion Γ›


open AlgebraicGeometry CategoryTheory Limits in
theorem _root_.GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver :
    ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (G : Over S)
      (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ S) (B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver B.hom := by
  intro R A _ _ S s G y B φ hG hq hpb
  let j : R →+* A :=
    (Spec.preimage (y ≫ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))).hom
  have hj : y ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    simp only [j, CommRingCat.ofHom_hom]
    exact (Spec.map_preimage _).symm
  haveI := isImmersion_pullback_lift_of_isPullback G.hom s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) y hj φ B.hom hpb
  haveI : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) hpb hG
  have hqQ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) :=
    (_root_.GlobalTheory.isQProjOver_baseChange_and_finite_restrict R A j _ _).1 hq
  have he : pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) = B.hom := pullback.lift_snd _ _ _
  haveI : IsProper (pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) := by rw [he]; infer_instance
  rw [← he]
  exact _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion _ hqQ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem exists_lift_of_surjectiveOnStalks {X Z : Scheme.{0}} (j : X ⟶ Z) [SurjectiveOnStalks j]
    (K : Type) [Field K] (t : Spec (.of K) ⟶ Z) (x : X)
    (hx : t (IsLocalRing.closedPoint K) = j x) :
    ∃ u : Spec (.of K) ⟶ X, u ≫ j = t ∧ ∀ p, u p = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective t
  obtain rfl : z = j x := (Scheme.fromSpecResidueField_apply z
    (Spec.map φ (IsLocalRing.closedPoint K))).symm.trans hx
  have : IsIso (j.residueFieldMap x) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
    refine ⟨Z.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (inv (j.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_, fun p => by simp⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem isClosedImmersion_of_lift {X Z : Scheme.{0}} [IsLocallyNoetherian Z] [Z.IsSeparated]
    (j : X ⟶ Z) [IsPreimmersion j] [QuasiCompact j]
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K]
      (x : Sp K ⟶ X) (y : Sp V ⟶ Z), Set.range x ⊆ genericPoints X →
      x ≫ j = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (IsClosedMap.isClosed_range ?_)
  rw [isClosedMap_iff_specializingMap]
  refine j.isEmbedding.isInducing.specializingMap ?_
  rintro _ z hz ⟨x, rfl⟩
  obtain ⟨x₀, hx₀, hs⟩ := exists_mem_genericPoints_specializes x
  have hs' : j x₀ ⤳ z := (hs.map j.continuous).trans hz
  by_cases hne : j x₀ = z
  · exact ⟨x₀, hne⟩
  obtain ⟨O, _, _, _, g, hg₀, hg₁⟩ := exists_complete_discreteValuationRing_of_specializes hs' hne
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hpt : (spMap (algebraMap O (FractionRing O)) ≫ g)
      (IsLocalRing.closedPoint (FractionRing O)) = j x₀ := by
    refine Eq.trans (congrArg g (PrimeSpectrum.ext ?_)) hg₀
    change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨u, hu, hux⟩ := exists_lift_of_surjectiveOnStalks j (FractionRing O) _ x₀ hpt
  obtain ⟨x', hx'⟩ := h O (FractionRing O) u g (by rintro _ ⟨p, rfl⟩; rw [hux]; exact hx₀) hu
  have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
    refine ⟨?_⟩
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have e : x' ≫ j = g :=
    ext_of_isDominant (spMap (algebraMap O (FractionRing O))) (by rw [← Category.assoc, hx', hu])
  exact ⟨x' (IsLocalRing.closedPoint O), by rw [← hg₁, ← e]; rfl⟩

theorem isProper_of_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro R _ _ X Y _ f s hs ⟨N, i, hi, hq, e⟩ h
  have := isProper_str R N
  let j : X ⟶ pullback s (PSpace.str R N) := pullback.lift f i e.symm
  have hj₁ : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.snd _ _) := hj₂ ▸ hi
  have : QuasiCompact (j ≫ pullback.snd _ _) := hj₂ ▸ hq
  have : IsImmersion j := IsImmersion.of_comp j (pullback.snd _ _)
  have : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd _ _)
  have : IsLocallyNoetherian (pullback s (PSpace.str R N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have : (pullback s (PSpace.str R N)).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst s (PSpace.str R N) ≫ s)]
    infer_instance
  have : IsClosedImmersion j := isClosedImmersion_of_lift j fun V K _ _ _ _ _ _ _ x y hx hy =>
    h V K x (y ≫ pullback.fst _ _) hx (by rw [← hj₁, ← Category.assoc, hy, Category.assoc])
  rw [← hj₁]
  infer_instance

end GlobalTheory.ValuativeGeneric
end

