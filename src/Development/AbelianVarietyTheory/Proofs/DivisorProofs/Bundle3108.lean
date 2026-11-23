module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpSchemeSquareProductMapEqTensorHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerDet

variable {S : Scheme.{0}}

theorem comp_pow_id {A B : Over S} [GrpObj B] (f : A ⟶ B) (n : ℕ) : f ≫ (𝟙 B) ^ n = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem pow_id_comp {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    ((𝟙 A) ^ n) ≫ f = f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih, Category.id_comp]

theorem epi_pow_id (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (c : ℕ) (hc : 0 < c) :
    Epi ((𝟙 A) ^ c : A ⟶ A) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A hA c hc
  exact GlobalTheory.FlatQuotient.epi_of_flat_surjective _

theorem exists_factor {A A₁ A₂ : Over S} [GrpObj A] [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂]
    (hA : IsAbelianScheme A) (hA₁ : IsAbelianScheme A₁) (c : ℕ) (hc : 0 < c)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) (ψ' : A₁ ⟶ A) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsMonHom ψ']
    (h₁ : ψ₁ ≫ ψ' = (𝟙 A) ^ c) (h₂ : ψ' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ ψ₁ = 1 → x ≫ ψ₂ = 1) :
    ∃ β : A₁ ⟶ A₂, IsMonHom β ∧ ψ₁ ≫ β = ψ₂ := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S A₁ hA₁ c hc
  rw [← h₂] at h1 h2 h3
  have hpb := IsPullback.of_hasPullback (ψ' ≫ ψ₁) (η[A₁])
  have ht : pullback.snd (ψ' ≫ ψ₁) (η[A₁]) = toUnit _ := toUnit_unique _ _
  rw [ht] at hpb
  obtain ⟨β, hβ, e⟩ := GlobalTheory.FlatQuotient.exists_desc (ψ' ≫ ψ₁) _ (ψ' ≫ ψ₂) hpb (by
    rw [← Category.assoc, ← Hom.one_def]
    refine hk _ _ ?_
    rw [Category.assoc, hpb.w, Hom.one_def])
  refine ⟨β, hβ, ?_⟩
  have := epi_pow_id A hA c hc
  rw [← cancel_epi ((𝟙 A) ^ c), ← Category.assoc, pow_id_comp, ← comp_pow_id, ← h₂, Category.assoc, e,
    ← Category.assoc, h₁]


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem pic_eq_zero_of_pull {X B : Over S} [GrpObj X] [GrpObj B] (hX : IsAbelianScheme X)
    (hB : IsAbelianScheme B) (k : ℕ) (hk : 0 < k) (χ : X ⟶ B) (χ' : B ⟶ X) [IsMonHom χ]
    (hc : χ' ≫ χ = (𝟙 B) ^ k) (d : Pic (B ⊗ B).left)
    (d₁ : pull (lift (1 : B ⟶ B) (𝟙 B)).left d = 0) (d₂ : pull (lift (𝟙 B) (1 : B ⟶ B)).left d = 0)
    (dχ : pull (χ ⊗ₘ χ).left d = 0) : d = 0 := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S B hB k hk
  have hD : pull (χ ⊗ₘ 𝟙 B).left d = 0 := by
    refine pic_eq_zero_of_fpqc X B B hX ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ X) (𝟙 B) ≫ (χ ⊗ₘ 𝟙 B) = lift (1 : B ⟶ B) (𝟙 B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₁]
    · rw [← pull_comp_left]
      have : lift (fst X B) (snd X B ≫ (𝟙 B) ^ k) ≫ (χ ⊗ₘ 𝟙 B) =
          lift (fst X B) (snd X B ≫ χ') ≫ (χ ⊗ₘ χ) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, dχ, map_zero]
  have hQ : pull (lift (snd B B) (fst B B)).left d = 0 := by
    refine pic_eq_zero_of_fpqc B B B hB ((𝟙 B) ^ k) hfl hsu hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : B ⟶ B) (𝟙 B) ≫ lift (snd B B) (fst B B) = lift (𝟙 B) (1 : B ⟶ B) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, d₂]
    · rw [← pull_comp_left]
      have : lift (fst B B) (snd B B ≫ (𝟙 B) ^ k) ≫ lift (snd B B) (fst B B) =
          lift (snd B B ≫ χ') (fst B B) ≫ (χ ⊗ₘ 𝟙 B) := by
        rw [← hc]; apply CartesianMonoidalCategory.hom_ext <;> simp
      rw [this, pull_comp_left, hD, map_zero]
  have hsw : lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B) = 𝟙 (B ⊗ B) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have H : pull (lift (snd B B) (fst B B) ≫ lift (snd B B) (fst B B)).left d = d := by
    rw [hsw, Over.id_left, pull_id]
  rw [pull_comp_left, hQ, map_zero] at H
  exact H.symm

theorem grpSchemeSquareProductMap_eq_tensorHom {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    sq2 ψ = (ψ ⊗ₘ ψ).left := by
  have : lift (fst A A ≫ ψ) (snd A A ≫ ψ) = ψ ⊗ₘ ψ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  exact congrArg (fun f : A ⊗ A ⟶ A' ⊗ A' => f.left) this


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem exists_objMap_of_ker_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ → (∀ (T : Over S) (x : T ⟶ o.A), x ≫ ψ₁ = 1 ↔ x ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.φ = ψ₂.left := by
  intro p _ D R _ b N _ _ c S _ s o o₁ o₂ ψ₁ ψ₂ H₁ H₂ hk
  have hc := H₁.pos
  obtain ⟨-, m₁, a₁, l₁, ⟨P₁⟩, ψ₁', m₁', u₁, v₁⟩ := H₁
  obtain ⟨-, m₂, a₂, l₂, ⟨P₂⟩, ψ₂', m₂', u₂, v₂⟩ := H₂
  obtain ⟨β, hβ, e⟩ := exists_factor o.ab o₁.ab c hc ψ₁ ψ₂ ψ₁' u₁ v₁ fun T x => (hk T x).1
  obtain ⟨β', -, e'⟩ := exists_factor o.ab o₂.ab c hc ψ₂ ψ₁ ψ₂' u₂ v₂ fun T x => (hk T x).2
  have E₁ : Epi ψ₁ := by
    have := epi_pow_id o₁.A o₁.ab c hc
    exact epi_of_epi_fac v₁
  have E₂ : Epi ψ₂ := by
    have := epi_pow_id o₂.A o₂.ab c hc
    exact epi_of_epi_fac v₂
  let i : o₁.A ≅ o₂.A := ⟨β, β', by rw [← cancel_epi ψ₁, ← Category.assoc, e, e', Category.comp_id],
    by rw [← cancel_epi ψ₂, ← Category.assoc, e', e, Category.comp_id]⟩
  have hpol : LBIso o₁.P (o₂.P.pull (β ⊗ₘ β).left) := by
    have hN : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    rw [grpSchemeSquareProductMap_eq_tensorHom] at P₁ P₂
    let p₁ := cls o₁.P o₁.isLB
    let p₂ := cls o₂.P o₂.isLB
    have n₁ : pull (ψ₁ ⊗ₘ ψ₁).left p₁ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₁.isLB _)).2 P₁).symm
    have n₂ : pull (ψ₂ ⊗ₘ ψ₂).left p₂ = cls _ hN := ((cls_eq_iff hN (pull_isLB o₂.isLB _)).2 P₂).symm
    have r₁₁ : pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₁
    have r₁₂ : pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left p₁ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₁.isLB _)).2 o₁.rig₂
    have r₂₁ : pull (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₁
    have r₂₂ : pull (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left p₂ = 0 :=
      (cls_eq_zero_iff (pull_isLB o₂.isLB _)).2 o₂.rig₂
    have e₁ : lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₂ : lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A) ≫ (β ⊗ₘ β) = β ≫ lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have hd : pull (β ⊗ₘ β).left p₂ - p₁ = 0 := by
      refine pic_eq_zero_of_pull o.ab o₁.ab c hc ψ₁ ψ₁' v₁ _ ?_ ?_ ?_
      · rw [map_sub, r₁₁, sub_zero, ← pull_comp_left, e₁, pull_comp_left, r₂₁, map_zero]
      · rw [map_sub, r₁₂, sub_zero, ← pull_comp_left, e₂, pull_comp_left, r₂₂, map_zero]
      · rw [map_sub, n₁, ← pull_comp_left, tensorHom_comp_tensorHom, e, n₂, sub_self]
    exact (cls_eq_iff o₁.isLB (pull_isLB o₂.isLB _)).1 (sub_eq_zero.1 hd).symm
  refine ⟨{ φ := β.left, φ₂ := (β ⊗ₘ β).left
            cart := (GlobalTheory.TQCompare.isGrpPullback_id_iff _).2 ⟨i, hβ, rfl⟩
            sq := ⟨?_, ?_⟩, act := fun a => ?_, pol := hpol, eta := fun y => ?_ }, ?_⟩
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_fst]
  · rw [← Over.comp_left, ← Over.comp_left, tensorHom_snd]
  · rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← cancel_epi ψ₁, ← Category.assoc, ← a₁, Category.assoc, e, a₂, ← Category.assoc, e]
  · rw [← Over.comp_left, l₁, l₂, Category.assoc, e]
    exact (Category.id_comp _).symm
  · show ψ₁.left ≫ β.left = _
    rw [← Over.comp_left, e]

end GlobalTheory.UPel.HT.ES.KerDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HTRank

theorem finrank_quot_mSub : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) = r := by
  intro k _ _ C _ _ _ H _ _ _ σ r hP hc χ
  have e1 := GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k C H σ r hc χ
  have e2 := GlobalTheory.T.finrank_weightSpace_projective_tensor_eq k C H σ hP χ
  have hpos := GlobalTheory.T.weightSpace_tensor_ringHom_finrank_pos k C χ
  rw [e1] at e2
  exact (Nat.eq_of_mul_eq_mul_right hpos e2).symm

theorem finrank_quot : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ i, Module.finrank k (HdR o₀.A ⧸ GlobalTheory.HTRho.mSub (GlobalTheory.HTCount.crysAct o₀) (β.comp (b.t i)) ⊤) = D.m * D.n := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht i
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  haveI := hfd
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o₀.geom k (𝟙 _) β (by rw [Category.id_comp, ht])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O c)) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o₀.A o₀.ab (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.HTCount.crysAct_apply, e, GlobalTheory.T.charpoly_la_eq_pow p D c]
  have hproj := GlobalTheory.CrysProj.hdR_projective D.F k o₀.A o₀.ab (o₀.act.toF D)
  exact finrank_quot_mSub k (𝓞 D.F) (HdR o₀.A) ((GlobalTheory.HTCount.crysAct o₀).comp (algebraMap (𝓞 D.F) D.O))
    (D.m * D.n) hproj hc (β.comp (b.t i))

end GlobalTheory.HTRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogeny
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem lie_of_isQuasiInv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq act' hact
  obtain ⟨e, rfl⟩ := hc
  have hcY : IsUnit (((p ^ e : ℕ) : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_pow, map_natCast] at this
    rw [Nat.cast_pow]
    exact this
  obtain ⟨-, hEt, -⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B (p ^ e) ψ ψ' o.ab hB hcY hq
  haveI : IsMonHom ψ := hq.1
  haveI : Etale ψ.left := hEt
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ B).left := by
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left =
            (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i a => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i a).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ B).left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i a).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) Y o.A B ψ (o.act.toF D) (act'.toF D) inferInstance hEt
      (fun a => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  first | (exact @GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (exact GlobalTheory.HTDeform.liftFil_isCompl_red_stable) | (intros; apply GlobalTheory.HTDeform.liftFil_isCompl_red_stable  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLieStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  first | (exact @GlobalTheory.HTLiftLie.lie_liftFil) | (exact GlobalTheory.HTLiftLie.lie_liftFil) | (intros; apply GlobalTheory.HTLiftLie.lie_liftFil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandIsotropic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open IsLocalRing GlobalTheory.AbDual

namespace GlobalTheory.HTLiftIso

theorem liftFil_isotropic : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) m.cart, ∀ y ∈ liftFil (divided₂ hsq) m.cart, φ x y = 0 := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _ φ hφ x hx y hy
  let κ := GlobalTheory.Cris.divided₂ hsq
  have hκ : GlobalTheory.Cris.IsNilDP κ := GlobalTheory.Cris.isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have CS := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl o.ab hg o.ab hg m.cart m.cart
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have CD := cupSquare_of_free ADR.1 hAB (smooth_prod hg hg)
  obtain ⟨φd, hφd⟩ := exists_isCorrForm CD o.isLB o.rig₁ o.rig₂
  obtain ⟨φ₀, hφ₀, e₀⟩ := GlobalTheory.Published.AbelianDualCrystal.exists_crystal_pairing κ m.cart m.cart m.sq.1 m.sq.2
    o.isLB o₀.isLB (LBIso.symm m.pol) hφd
  obtain rfl := hφ.unique CS o₀.isLB hφ₀
  rw [e₀]
  obtain ⟨ψ, hψ, eψ⟩ := hφd.isPolForm
  have iso := (ADR.2.2.2.2 C _ _ hAB (smooth_prod hg hg) o.P o.isLB ψ hψ).1
  have hx' : crysToDR κ m.cart x ∈ Fil o.A := hx
  have hy' : crysToDR κ m.cart y ∈ Fil o.A := hy
  have h := iso _ (push_mem_Fil (inl o.A o.A) hx') _ (push_mem_Fil (inr o.A o.A) hy')
  rw [eψ, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_push _ _ _ (lift_fst _ _),
    push_push _ _ _ (lift_snd _ _)] at h
  simpa [push_id, push_one] using h

end GlobalTheory.HTLiftIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → ∀ v : GlobalTheory.UPel.HT.epsPtR x ⟶ A, GlobalTheory.UPel.HT.IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (GlobalTheory.UPel.HT.epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, GlobalTheory.UPel.HT.IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod := by
  first | (exact @GlobalTheory.HTDefLift.lie_of_liftFil) | (exact GlobalTheory.HTDefLift.lie_of_liftFil) | (intros; apply GlobalTheory.HTDefLift.lie_of_liftFil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_structures_relatively_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  first | (exact @GlobalTheory.UPel.HT.relRep_htPull) | (exact GlobalTheory.UPel.HT.relRep_htPull) | (intros; apply GlobalTheory.UPel.HT.relRep_htPull  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (iota : Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) →+* (FractionRing Ω)) (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, iota (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = (algebraMap Ω (FractionRing Ω)) (φ r)) ∧ (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (iota.mapMatrix Θ₁) u' p p' k s)) := by
  first | exact @GlobalTheory.HeatV.heat_values_of_isKS | exact GlobalTheory.HeatV.heat_values_of_isKS | (intros; apply GlobalTheory.HeatV.heat_values_of_isKS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenNearOfFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  first | (exact @GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre) | (exact GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre) | (intros; apply GlobalTheory.KerKilledFibreOpen.kerKilledOn_near_of_fibre  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFilStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  first | (exact @GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (exact GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (intros; apply GlobalTheory.HTCount.lieZ_mem_fil_and_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β → ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  first | (exact @GlobalTheory.HTCount.lieZ_le_Fil) | (exact GlobalTheory.HTCount.lieZ_le_Fil) | (intros; apply GlobalTheory.HTCount.lieZ_le_Fil  <;> assumption)
end

