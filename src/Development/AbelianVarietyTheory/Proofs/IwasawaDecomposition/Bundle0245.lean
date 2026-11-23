module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycBasic
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0651
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKsOfKur
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN.SelfGood

variable {l : ℕ} [Fact l.Prime]

theorem sqrt_mem (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) (S : IntermediateField ℚ_[l] (Loc.Om l))
    (hS : ∀ z : Loc.Om l, z ^ p = 1 → z ∈ S) (x : Loc.Om l) (hx : x ^ 2 = -(p : Loc.Om l)) : x ∈ S := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Loc.Om l) p
  let ψ : AddChar (ZMod p) (Loc.Om l) := AddChar.zmodChar p hw.pow_eq_one
  have hψ : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hw
  let χ : MulChar (ZMod p) (Loc.Om l) := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom (Loc.Om l))
  have hch : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; omega
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective)).2 (quadraticChar_ne_one hch)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have hneg : χ (-1) = -1 := by
    have : quadraticChar (ZMod p) (-1) = -1 := by
      rw [quadraticChar_neg_one hch, ZMod.card, ZMod.χ₄_nat_three_mod_four h4]
    simp [χ, MulChar.ringHomComp_apply, this]
  have hmu : ∀ a, ψ a ∈ S := fun a => hS _ (by
    rw [AddChar.zmodChar_apply, ← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow])
  have hg : gaussSum χ ψ ^ 2 = -(p : Loc.Om l) := by
    rw [gaussSum_sq hχ1 hχq hψ, hneg, ZMod.card]; simp
  have hm : gaussSum χ ψ ∈ S := by
    unfold gaussSum
    exact sum_mem fun a _ => mul_mem (intCast_mem _ _) (hmu a)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans hg.symm) with h | h
  · rw [h]; exact hm
  · rw [h]; exact neg_mem hm

theorem root_mem_Kur {z : Loc.Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : z ^ m = 1) :
    z ∈ Loc.MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

end GlobalTheory.MemN.SelfGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberPeriodAtTrivialPositionSpec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TrueRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {θ : InfF D}

abbrev cuspIn (θ : InfF D) (V : HSp D) : Submodule ℂ (AFs θ V) := (CuspS θ V).comap (AFs θ V).subtype

def cuspEq (θ : InfF D) (V : HSp D) : cuspIn θ V ≃ₗ[ℂ] CuspS θ V := Submodule.comapSubtypeEquivOfLe (CuspS_le θ V)

theorem mem_cuspIn (hθ : IsInfFam θ) {V : HSp D} (F : AFs θ V) : F ∈ cuspIn θ V ↔ IsCuspFun V F.1 :=
  (mem_CuspS (formSub D) hθ).trans ⟨fun h => h.2, fun h => ⟨aut hθ F, h⟩⟩

def trE (hθ : IsInfFam θ) (V : HSp D) (k : GA D V) (hk : ∀ φ, IsAutFunSm θ V φ → IsAutFunSm θ V (rTr V k φ)) :
    Module.End ℂ (AFs θ V) :=
  (LinearMap.funLeft ℂ ℂ fun g => g * k).restrict fun φ hφ => Submodule.subset_span (hk φ (aut hθ ⟨φ, hφ⟩))

theorem trE_cusp (hθ : IsInfFam θ) (V : HSp D) (k hk) (F : AFs θ V) (hF : F ∈ cuspIn θ V) : trE hθ V k hk F ∈ cuspIn θ V := by
  rw [mem_cuspIn hθ] at hF ⊢
  exact (_root_.GlobalTheory.Mem.Th.isCuspFun_closed D V _ _ (aut hθ F).toIsAutFun (aut hθ F).toIsAutFun hF hF).2.2.1 k

def actFin (hθ : IsInfFam θ) (V : HSp D) : GfC V →* Module.End ℂ (AFs θ V) where
  toFun k := trE hθ V k fun φ h => _root_.GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin D θ hθ V φ h k k.2
  map_one' := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_one g))
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (funext fun g => congrArg φ.1 (mul_assoc g a b).symm)


open Classical in
def actReal (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Module.End ℂ (AFs θ V) :=
  if h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then trE hθ V (atTau θ V τ g) fun φ hφ => GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace D θ hθ V φ hφ τ g h else 1

theorem actReal_apply (hθ : IsInfFam θ) (V : HSp D) (τ) {g} (h : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (F : AFs θ V) (x) :
    (actReal hθ V τ g F).1 x = F.1 (x * atTau θ V τ g) := by
  rw [actReal, dif_pos h]; rfl

theorem mul_mem_UH {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H) (hh : h ∈ Formalism.QuantumDeterminants.UH H) :
    g * h ∈ Formalism.QuantumDeterminants.UH H := by
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at *
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]

def chrGrp (D : D7) : Subgroup (IdC D) := (_root_.GlobalTheory.Mem.HeckeExp.hecke_exp_laws D).1.choose

theorem mem_chrGrp {χ : IdC D} : χ ∈ chrGrp D ↔ IsHC D χ := (_root_.GlobalTheory.Mem.HeckeExp.hecke_exp_laws D).1.choose_spec χ

def expo (χ : chrGrp D) (τ : D.what₂.Tau) : ℚ := ((mem_chrGrp.1 χ.2).2 τ).choose

theorem expo_spec (χ : chrGrp D) (τ : D.what₂.Tau) : HasInfExp D χ.1 τ (expo χ τ) := ((mem_chrGrp.1 χ.2).2 τ).choose_spec

theorem expo_eq {χ : chrGrp D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ.1 τ a) : expo χ τ = a :=
  (_root_.GlobalTheory.Mem.HeckeExp.hecke_exp_laws D).2.1 _ _ _ _ (expo_spec χ τ) h

def ksph (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Subgroup (GfC V) :=
  (_root_.GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V S).choose.subgroupOf (GfC V)

theorem mem_ksph {V : HSp D} {S} {g : GfC V} : g ∈ ksph V S ↔ (g : GA D V) ∈ KsphC V S := by
  rw [← (_root_.GlobalTheory.Mem.Ksph.exists_subgroup_ksph D V S).choose_spec.1]; rfl


open Classical in
def transp {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Φ : ThS ψ V W) : ThS ψ W V :=
  if h : IsThetaFun ψ W V (fun x => Φ.1 x.transpose) then ⟨_, mem_ThS.2 h⟩ else 0

theorem transp_apply {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} (h : V.rank ≠ W.rank)
    (Φ : ThS ψ V W) (x : WA V W) : (transp Φ).1 x.transpose = Φ.1 x := by
  rw [transp, dif_pos ((GlobalTheory.Mem.ThetaClosed.thetaFun_closed D ψ hψ V W Φ.1).2.2 h (mem_ThS.1 Φ.2))]
  rfl

abbrev Trip (D : D7) := Σ (A B : HSp D), A.V →ₗ[D.host.E] B.V

abbrev trip0 (D : D7) : Trip D := ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0⟩

def Bes1 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type := {d : BesDat A B ι // (d.y : GA D B) = 1}

def Is0 (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop := (⟨A, B, ι⟩ : Trip D) = trip0 D

def PosT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  (Odd (B.rank - A.rank) → Bes1 A B ι) ⊕ (D.what₂.Word × PLift (Is0 A B ι))

abbrev Ses (θ : InfF D) (A B : HSp D) : Type := AFs θ A →ₗ⋆[ℂ] CuspS θ B →ₗ[ℂ] ℂ

def bes0 (u : D.what₂.Word) : Bes1 (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) := ⟨memberBes D u, rfl⟩

def datT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (ho : Odd (B.rank - A.rank)) : PosT A B ι → Bes1 A B ι
  | .inl f => f ho
  | .inr x => cast (congrArg (fun t : Trip D => Bes1 t.1 t.2.1 t.2.2) x.2.down.symm) (bes0 x.1)

theorem inr_eq (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) :
    (⟨A, B, ι, .inr x⟩ : Σ (A A' : HSp D) (ι : A.V →ₗ[D.host.E] A'.V), PosT A A' ι) =
      ⟨D.sp.X 0, D.sp.Y 0, D.sp.iXY 0, .inr (x.1, ⟨rfl⟩)⟩ := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  rfl

theorem inr_ne (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (x : D.what₂.Word × PLift (Is0 A B ι)) (f) :
    ¬ HEq (.inr x : PosT A B ι) (.inl f : PosT (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)) := by
  obtain ⟨u, ⟨h⟩⟩ := x
  cases h
  intro h
  cases eq_of_heq h

section Scale

variable {P Q R : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] [AddCommGroup R] [Module ℂ R]
  (a : ℂ) (b : P →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (e : R ≃ₗ[ℂ] Q)

theorem ses_add (x x' : P) (y : Q) : a * b (x + x') y = a * b x y + a * b x' y := by simp [mul_add]

theorem ses_smul (c : ℂ) (x : P) (y : Q) : a * b (c • x) y = star c * (a * b x y) := by simp [mul_left_comm]

theorem ses_right (x : P) : IsLinearMap ℂ fun y : R => a * b x (e y) :=
  ⟨fun G G' => by simp [mul_add], fun c G => by simp [mul_left_comm]⟩

end Scale

section Record

variable (hP : PetInt D) (hT : TopInt D) (hB : BesInt D) (hL : LiftAut D) (hθ : IsInfFam θ)
  {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (Wf : WeilFun D ψ) (Tw : Tow D) (Rc : RecFun D θ ψ)

def per1 (u : D.what₂.Word) : Ses θ (D.sp.X 0) (D.sp.Y 0) :=
  ((_root_.GlobalTheory.RootExch.PosLinear.posLin D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0) (D.sp.X_def 0 (Nat.zero_le _))).choose


open Classical in
def perT (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : PosT A B ι → Ses θ A B
  | .inl f => if ho : Odd (B.rank - A.rank) then (exists_bes hB hθ hψ (f ho).1).choose else 0
  | .inr x => cast (congrArg (fun t : Trip D => Ses θ t.1 t.2.1) x.2.down.symm) (per1 hθ hψ Rc x.1)

theorem perT_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank))
    (f : Odd (B.rank - A.rank) → Bes1 A B ι) :
    perT hB hθ hψ Rc A B ι (.inl f) = (exists_bes hB hθ hψ (f ho).1).choose := dif_pos ho

theorem perT_inr (u : D.what₂.Word) :
    perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) = per1 hθ hψ Rc u := rfl

theorem clause_inl {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (ho : Odd (B.rank - A.rank)) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (f : Odd (B.rank - A.rank) → Bes1 A B ι) {μ 𝓕} (hμ : IsVolPair D A μ 𝓕)
    {s : GA D A → GA D B} (hs : ∀ h, EmbRel B A ι (s h) h) (φ : AFs θ A) (F : cuspIn θ B) (hφ : IsAniso A ∨ φ ∈ cuspIn θ A) :
    GlobalTheory.BesselCompare.ClauseFlag ψ (f ho).1 μ 𝓕 s φ.1 F.1.1 (Rc.petC A)
      ((Rc.petC A : ℂ) * perT hB hθ hψ Rc A B ι (.inl f) φ (cuspEq θ B F)) := by
  intro ν 𝓝 h1 h2 h3
  have h := (exists_bes hB hθ hψ (f ho).1).choose_spec hA hι μ 𝓕 hμ s hs φ (cuspEq θ B F) hφ ν 𝓝 h1 h2 h3
  rw [perT_inl hB hθ hψ Rc ho f, h, one_mul]
  rfl

theorem memberPeriodAtTrivialPosition_spec (u : D.what₂.Word) {μ 𝓕} (hμ : IsVolPair D (D.sp.X 0) μ 𝓕) {ν 𝓝} (hν : (Rc.per1.dat u).bes.IsUnitPair ν 𝓝)
    {s : GA D (D.sp.X 0) → GA D (D.sp.Y 0)} (hs : ∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h)
    (φ : AFs θ (D.sp.X 0)) (F : cuspIn θ (D.sp.Y 0)) :
    (Rc.petC (D.sp.X 0) : ℂ) * perT hB hθ hψ Rc (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (.inr (u, ⟨rfl⟩)) φ (cuspEq θ _ F) =
      (Rc.petC (D.sp.X 0) : ℂ) * (Rc.per1.dat u).period ψ μ 𝓕 ν 𝓝 s (fun g => star (φ.1 g)) F.1.1 := by
  rw [perT_inr, per1, ← ((_root_.GlobalTheory.RootExch.PosLinear.posLin D).2.2 θ hθ ψ hψ _ _ _ (Rc.per1.dat u) (D.sp.X_sig 0)
    (D.sp.X_def 0 (Nat.zero_le _))).choose_spec μ 𝓕 hμ ν 𝓝 hν s hs φ (cuspEq θ _ F)]
  rfl

theorem adm {V W : HSp D} (χ χ' : chrGrp D) (h : V.rank ≠ W.rank) (h1 : ResEta D χ.1 V.rank) (h2 : ResEta D χ'.1 W.rank) :
    admitted V W χ.1 χ'.1 := ⟨h, mem_chrGrp.1 χ.2, mem_chrGrp.1 χ'.2, h1, h2⟩

theorem range_ThS (V W : HSp D) : Set.range (ThS ψ V W).subtype = {f | IsThetaFun ψ V W f} :=
  Set.ext fun f => ⟨fun ⟨x, hx⟩ => hx ▸ mem_ThS.1 x.2, fun h => ⟨⟨f, mem_ThS.2 h⟩, rfl⟩⟩

end Record

end GlobalTheory.Mem.TrueRecord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModEqOneOfNorm
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelChoice

theorem mod_eq_one_of_norm {E : Type} [Field E] [NumberField E] (c : E →+* E) (π : 𝓞 E) (p m : ℕ) (hm : 1 < m)
    (hn : (π : E) * c (π : E) = (p : E)) (hc : π - 1 ∈ Ideal.span {((m : ℕ) : 𝓞 E)}) : p % m = 1 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
  have hπ : (π : E) = 1 + (a : E) * (m : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) ha
    simp only [map_mul, map_natCast, map_sub, map_one] at h
    change (a : E) * (m : E) = (π : E) - 1 at h
    rw [h]; ring
  have hai : IsIntegral ℤ (a : E) := a.2
  have hci : IsIntegral ℤ (c (a : E)) := hai.map c.toIntAlgHom
  have hmi : IsIntegral ℤ ((m : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a) := by
    rw [map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add (f := _), map_one, map_mul, map_natCast]
    field_simp
    ring
  have hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m)) := by
    rw [hx]
    exact (hai.add hci).add (hmi.mul (hai.mul hci))
  have hqi : IsIntegral ℤ (((p : ℚ) - 1) / m) :=
    (isIntegral_algebraMap_iff ).1 hxi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqi
  have hk' : ((p : ℚ) - 1) = (k : ℚ) * m := by
    have : (k : ℚ) = ((p : ℚ) - 1) / m := by simpa using hk
    rw [this]; field_simp
  have hz : (p : ℤ) = 1 + (m : ℤ) * k := by
    have : ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : ((p % m : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, hz, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)
  exact_mod_cast h1

theorem exists_levCh : ∀ (P : PreCh) (du : P.Word → ℕ) (Ds Ga : ℝ), (∀ u, 0 < du u) → 0 < Ds → 1 < Ga → (∀ u, ∃ (π : 𝓞 P.H.E) (p : ℕ), p.Prime ∧ p ≠ P.H.pde ∧ p ≠ P.H.pde' ∧ (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (p : P.H.E) ∧ π - 1 ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)} ∧ (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) * ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ L : LevCh P, L.duStar = du ∧ L.Dstar = Ds ∧ L.GamP = Ga := by
  intro P du Ds Ga hdu hDs hGa h
  choose π p hp h1 h2 hK hN hc hlo hhi using h
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.H.QS := P.H.QS_pos
  have hm : 1 < P.H.QS * P.H.q * P.H.d := by
    have hq : 0 < P.H.q := by omega
    have hd : 0 < P.H.d := by omega
    have h1 : P.H.q ≤ P.H.QS * P.H.q := Nat.le_mul_of_pos_left _ hn
    have h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_right _ hd
    omega
  have hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1 := fun u => by
    refine mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_
    refine Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)
    exact Nat.cast_dvd_cast (Dvd.intro _ rfl)
  exact ⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc,
           T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs,
           GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl⟩

end GlobalTheory.Mem.LevelChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.WeilDeligne.IrrDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := _root_.GlobalTheory.GroundFieldChange.interNum_fieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
end

