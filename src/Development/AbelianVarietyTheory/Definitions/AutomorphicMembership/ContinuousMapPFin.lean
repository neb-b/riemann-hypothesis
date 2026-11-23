module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

@[simp] theorem RU_apply (x g : UA E n) (φ : UA E n → ℂ) : RU E n x φ g = φ (g * x) := rfl

theorem RU_RU (x y : UA E n) (φ : UA E n → ℂ) : RU E n x (RU E n y φ) = RU E n (x * y) φ := by
  rw [map_mul]; rfl

instance : (finU (E := E) (n := n)).Normal := MonoidHom.normal_ker _

instance : (infU E n).Normal := MonoidHom.normal_ker _

theorem fin_mul_inf {k x : UA E n} (hk : k ∈ finU (E := E) (n := n)) (hx : x ∈ infU E n) : k * x = x * k := by
  have h1 : GeneralLinearGroup.map (pInf E) k.1 = 1 := hk
  have h2 : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]


variable (E n) in
def autU : Submodule ℂ (UA E n → ℂ) where
  carrier := {φ | IsAutFormU φ}
  add_mem' {a b} ha hb := by
    refine ⟨ha.cont.add hb.cont, fun γ hγ g => by simp [ha.left γ hγ g, hb.left γ hγ g],
      (smoothPart ((RU E n).comp (finU (E := E) (n := n)).subtype)).add_mem ha.level hb.level, ?_⟩
    have := ha.kfin
    have := hb.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k a) ⊔
      Submodule.span ℂ (Set.range fun k : infU E n => RU E n k b)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
  zero_mem' := by
    refine ⟨continuous_const, fun _ _ _ => rfl, (smoothPart ((RU E n).comp (finU (E := E) (n := n)).subtype)).zero_mem, ?_⟩
    refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact map_zero (RU E n k)
  smul_mem' c {a} ha := by
    refine ⟨ha.cont.const_smul c, fun γ hγ g => by simp [ha.left γ hγ g],
      (smoothPart ((RU E n).comp (finU (E := E) (n := n)).subtype)).smul_mem c ha.level, ?_⟩
    have := ha.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E n => RU E n k a))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)

theorem mem_autU {φ : UA E n → ℂ} : φ ∈ autU E n ↔ IsAutFormU φ := Iff.rfl

theorem smooth_normal {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) [hN : N.Normal] (x : G) {v : V} (h : IsOpen {k : N | ρ k v = v}) :
    IsOpen {k : N | ρ k (ρ x v) = ρ x v} := by
  let c : N → N := fun k => ⟨x⁻¹ * k * x, hN.conj_mem' _ k.2 x⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  convert h.preimage hc using 1
  ext k
  change ρ k (ρ x v) = ρ x v ↔ ρ (x⁻¹ * k * x) v = v
  have hm : ∀ a b u, ρ a (ρ b u) = ρ (a * b) u := fun a b u => by rw [map_mul]; rfl
  constructor
  · intro e
    rw [mul_assoc, ← hm, ← hm, e, hm, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro e
    conv_rhs => rw [← e]
    rw [hm, hm, mul_assoc, mul_inv_cancel_left]

theorem RU_mem_autU (x : UA E n) (φ : UA E n → ℂ) (h : φ ∈ autU E n) : RU E n x φ ∈ autU E n := by
  refine ⟨h.cont.comp (continuous_mul_const x), fun γ hγ g => ?_, ?_, ?_⟩
  · rw [RU_apply, RU_apply, mul_assoc, h.left γ hγ]
  · exact smooth_normal (RU E n) (finU (E := E) (n := n)) x h.level
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)).map
      (RU E n x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨x⁻¹ * k * x, Subgroup.Normal.conj_mem' inferInstance _ k.2 x⟩, rfl⟩, ?_⟩
    simp only [RU_RU, mul_assoc, mul_inv_cancel_left]


variable (E n) in
def autRep : Representation ℂ (UA E n) (autU E n) := sub (RU E n) (autU E n) RU_mem_autU


variable (E n) in
abbrev Wt : Type := InfinitePlace E → DomWeight n

def zeroWt (n : ℕ) : DomWeight n := ⟨0, antitone_const⟩

theorem dual_dual (lam : DomWeight n) : lam.dual.dual = lam := by
  cases lam
  simp [DomWeight.dual]


open Classical in
def Wt.at (W : Wt E n) (τ : E →+* ℂ) : DomWeight n :=
  if (InfinitePlace.mk τ).embedding = τ then W (InfinitePlace.mk τ) else (W (InfinitePlace.mk τ)).dual


omit [NumberField E] [IsCMField E] in
@[simp] theorem Wt.at_embedding (W : Wt E n) (v : InfinitePlace E) : W.at v.embedding = W v := by
  simp [Wt.at]

theorem conjugate_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))

theorem Wt.at_conjugate (W : Wt E n) (τ : E →+* ℂ) : W.at (ComplexEmbedding.conjugate τ) = (W.at τ).dual := by
  unfold Wt.at
  rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact (conjugate_ne τ).symm)]
  · rw [if_pos h, if_neg (by rw [h]; exact conjugate_ne τ), dual_dual]


def Wt.ofFam (lam : (E →+* ℂ) → DomWeight n) : Wt E n := fun v => lam v.embedding

theorem Wt.at_ofFam {lam : (E →+* ℂ) → DomWeight n} (h : ∀ τ, lam (ComplexEmbedding.conjugate τ) = (lam τ).dual)
    (τ : E →+* ℂ) : (Wt.ofFam lam).at τ = lam τ := by
  unfold Wt.at Wt.ofFam
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · rw [if_pos e, e]
  · rw [if_neg (by rw [e]; exact conjugate_ne τ), e, h, dual_dual]

def infW (W : Wt E n) (τ : E →+* ℂ) : Multiset ℂ := infOfWeight (W.at τ)



def cAll : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) := MonoidHom.pi fun v => cEmb v.embedding

abbrev Wt.Sp (W : Wt E n) : Type := Formalism.L2.DIV.VV ℂ (ι := InfinitePlace E) W

def Wt.rep (W : Wt E n) : Representation ℂ (infU E n) W.Sp :=
  (Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (cAll.comp (infU E n).subtype)

instance (W : Wt E n) : FiniteDimensional ℂ W.Sp :=
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (W v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ W)

def algForms (W : Wt E n) : Submodule ℂ (W.Sp →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (W.rep x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

def postRep (W : Wt E n) : Representation ℂ (finU (E := E) (n := n)) (W.Sp →ₗ[ℂ] (UA E n → ℂ)) where
  toFun k := LinearMap.llcomp ℂ _ _ _ (RU E n k)
  map_one' := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_one g)
  map_mul' a b := LinearMap.ext fun f => LinearMap.ext fun v => funext fun g => congrArg (f v) (mul_assoc g a b).symm

@[simp] theorem postRep_apply (W : Wt E n) (k : finU (E := E) (n := n)) (f : W.Sp →ₗ[ℂ] (UA E n → ℂ)) (v : W.Sp) :
    postRep W k f v = RU E n k (f v) := rfl

theorem postRep_mem (W : Wt E n) (k : finU (E := E) (n := n)) (f : W.Sp →ₗ[ℂ] (UA E n → ℂ)) (h : f ∈ algForms W) :
    postRep W k f ∈ algForms W :=
  ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
    rw [postRep_apply, postRep_apply, h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩

def algRep (W : Wt E n) : Representation ℂ (finU (E := E) (n := n)) (algForms W) := sub (postRep W) (algForms W) (postRep_mem W)

theorem isSmooth_algRep (W : Wt E n) : IsSmooth (algRep W) := fun f => by
  let b := Module.finBasis ℂ W.Sp
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

def algForms.val {W : Wt E n} (f : algForms W) (g : UA E n) : Module.Dual ℂ W.Sp := (LinearMap.proj g).comp f.1

theorem algForms.val_left {W : Wt E n} (f : algForms W) {γ : UA E n} (hγ : γ ∈ ratU E n) (g : UA E n) :
    algForms.val f (γ * g) = algForms.val f g := LinearMap.ext fun v => (f.2.1 v).left γ hγ g

theorem algForms.val_right {W : Wt E n} (f : algForms W) (g : UA E n) (x : infU E n) :
    algForms.val f (g * x) = W.rep.dual x⁻¹ (algForms.val f g) := LinearMap.ext fun v => by
  rw [Representation.dual_apply, inv_inv]
  exact (congrFun (f.2.2 x v) g).symm

theorem algForms.val_algRep {W : Wt E n} (f : algForms W) (k : finU (E := E) (n := n)) (g : UA E n) :
    algForms.val (algRep W k f) g = algForms.val f (g * k) := rfl


variable (E n) in
@[ext] structure AutSub where

  V : Submodule ℂ (UA E n → ℂ)
  isAut : IsAutRepU V

namespace AutSub

variable (π π' : AutSub E n)

def rep : Representation ℂ (UA E n) π.V := sub (RU E n) π.V π.isAut.stable

@[simp] theorem rep_val (x : UA E n) (φ : π.V) : (π.rep x φ).1 = RU E n x φ.1 := rfl

theorem le_autU : π.V ≤ autU E n := π.isAut.aut

theorem isIrreducible_rep : π.rep.IsIrreducible := by
  refine (CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 π.isAut.ne_bot, fun W hW => ?_⟩
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  refine (π.isAut.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) ?_).imp
    (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans (Submodule.map_subtype_top _).symm)
  rintro x _ ⟨φ, hφ, rfl⟩
  exact ⟨_, hW x φ hφ, rfl⟩

def Iso : Prop := Nonempty (π.rep.Equiv π'.rep)


variable (E n) in
instance setoid : Setoid (AutSub E n) where
  r := Iso
  iseqv := ⟨fun π => ⟨.refl π.rep⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

def finPart (W : Wt E n) : Submodule ℂ (algForms W) :=
  ⨅ v : W.Sp, π.V.comap ((LinearMap.applyₗ v).comp (algForms W).subtype)


variable {π} in
theorem mem_finPart {W : Wt E n} {f : algForms W} : f ∈ π.finPart W ↔ ∀ v, f.1 v ∈ π.V := Submodule.mem_iInf _

def IsLocComp (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  IsCompAlong π.V (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ

def IsSat (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s q ∧ HasSatAt π.V w s ϖ q α

variable {π π'}

theorem Iso.exists_map (h : Iso π π') : ∃ T : π.V →ₗ[ℂ] (UA E n → ℂ), Function.Injective T ∧ (∀ φ, T φ ∈ π'.V) ∧
    ∀ x φ, T (π.rep x φ) = RU E n x (T φ) := by
  obtain ⟨e⟩ := h
  exact ⟨π'.V.subtype ∘ₗ e.toLinearMap, Subtype.val_injective.comp e.toLinearEquiv.injective, fun φ => (e φ).2,
    fun x φ => congrArg Subtype.val (LinearMap.congr_fun (e.isIntertwining' x) φ)⟩

theorem Iso.isCompAlong (h : Iso π π') {Gv : Subgroup (UA E n)} {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]
    {p : Gv →* H} {σ : Representation ℂ H W} (hσ : IsCompAlong π.V Gv p σ) : IsCompAlong π'.V Gv p σ := by
  obtain ⟨T, hi, hm, hT⟩ := h.exists_map
  obtain ⟨h1, f, h0, hf, h2⟩ := hσ
  refine ⟨h1, T ∘ₗ f.codRestrict _ hf, fun e => h0 (LinearMap.ext fun v => ?_), fun v => hm _, fun x v => ?_⟩
  · exact congrArg Subtype.val (hi ((LinearMap.congr_fun e v).trans (map_zero T).symm))
  · exact (congrArg T (Subtype.ext (h2 x v))).trans (hT x ⟨f v, hf v⟩)

theorem Iso.isUnramU (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} (hw : IsUnramU π.V w) : IsUnramU π'.V w := by
  obtain ⟨T, hi, hm, hT⟩ := h.exists_map
  obtain ⟨φ, hφ, h0, h1⟩ := hw
  refine ⟨T ⟨φ, hφ⟩, hm _, fun e => h0 (congrArg Subtype.val (hi (e.trans (map_zero T).symm))), fun x hx hk => ?_⟩
  rw [← hT]
  exact congrArg T (Subtype.ext (h1 x hx hk))

theorem Iso.isSat (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} {α : Fin (n / 2) → ℂˣ} (hα : π.IsSat w α) :
    π'.IsSat w α := by
  obtain ⟨s, ϖ, q, h1, h2, b, hb, h3, p, hp, σ, h4, h5⟩ := hα
  exact ⟨s, ϖ, q, h1, h2, b, hb, h3, p, hp, σ, h.isCompAlong h4, h5⟩

theorem IsLocComp.congr {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) (hπ : Iso π π') (hσ : Nonempty (σ.ρ.Equiv σ'.ρ)) : π'.IsLocComp w σ' := by
  obtain ⟨-, f, h0, hf, h2⟩ := hπ.isCompAlong h
  obtain ⟨e⟩ := hσ
  refine ⟨σ'.irred, f ∘ₗ e.symm.toLinearMap, fun h => h0 (LinearMap.ext fun v => ?_), fun v => hf _, fun x v => ?_⟩
  · exact (congrArg f (e.symm_apply_apply v)).symm.trans (LinearMap.congr_fun h (e v))
  · exact (congrArg f (LinearMap.congr_fun (e.symm.isIntertwining' _) v)).trans (h2 x _)

end AutSub


omit [IsCMField E] in
theorem continuous_map_pFin : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_snd)




variable (E n) in
def AU : Type := Quotient (AutSub.setoid E n)

namespace AU

def mk (π : AutSub E n) : AU E n := Quotient.mk _ π

theorem mk_surjective : Function.Surjective (mk : AutSub E n → AU E n) := Quotient.mk_surjective

def Sph (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Quotient.liftOn π (fun π => IsUnramU π.V w) fun _ _ h =>
    propext ⟨AutSub.Iso.isUnramU h, AutSub.Iso.isUnramU (Setoid.symm h)⟩

@[simp] theorem sph_mk (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) : (mk π).Sph w ↔ IsUnramU π.V w := Iff.rfl

def IsLoc (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) (σ : Irr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  Quotient.liftOn₂ π σ (fun π σ => π.IsLocComp w σ) fun _ _ _ _ h h' =>
    propext ⟨fun x => x.congr h h', fun x => x.congr (Setoid.symm h) (Setoid.symm h')⟩

def IsSat (π : AU E n) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  Quotient.liftOn π (·.IsSat w α) fun _ _ h => propext ⟨AutSub.Iso.isSat h, AutSub.Iso.isSat (Setoid.symm h)⟩

@[simp] theorem isSat_mk (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (n / 2) → ℂˣ) :
    (mk π).IsSat w α ↔ π.IsSat w α := Iff.rfl

def HasWt (π : AU E n) (τ : E →+* ℂ) (lam : DomWeight n) : Prop :=
  Quotient.liftOn π (fun π => HasWeightAt π.V τ lam) fun _ _ h =>
    propext ⟨AutSub.Iso.isCompAlong h, AutSub.Iso.isCompAlong (Setoid.symm h)⟩

@[simp] theorem hasWt_mk (π : AutSub E n) (τ : E →+* ℂ) (lam : DomWeight n) :
    (mk π).HasWt τ lam ↔ HasWeightAt π.V τ lam := Iff.rfl

theorem HasWt.conjugate {π : AU E n} {τ : E →+* ℂ} {lam : DomWeight n} (h : π.HasWt τ lam) :
    π.HasWt (ComplexEmbedding.conjugate τ) lam.dual := by
  obtain ⟨π, rfl⟩ := mk_surjective π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : lam.dual = lam := by
      cases lam
      unfold DomWeight.dual
      congr 1
      exact Subsingleton.elim _ _
    obtain ⟨hi, f, h0, h1, h2⟩ := h
    rw [e]
    refine ⟨hi, f, h0, h1, fun x v => Eq.trans ?_ (h2 ⟨x.1, GlobalTheory.DefiniteBC.embU_conjugate τ ▸ x.2⟩ v)⟩
    exact congrArg (fun g => f (GlobalTheory.Branching.sqRep ℂ 0 lam g v)) (Subsingleton.elim _ _)
  · exact GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn h

def wt (π : AU E n) : Wt E n := fun v => @Classical.epsilon _ ⟨zeroWt n⟩ (π.HasWt v.embedding)

theorem HasWt.wt {π : AU E n} {τ : E →+* ℂ} {lam : DomWeight n} (h : π.HasWt τ lam) : π.HasWt τ (π.wt.at τ) := by
  have key : ∀ (v : InfinitePlace E) (mu : DomWeight n), π.HasWt v.embedding mu → π.HasWt v.embedding (π.wt v) :=
    fun v mu hmu => Classical.epsilon_spec (p := π.HasWt v.embedding) ⟨mu, hmu⟩
  unfold Wt.at
  rcases InfinitePlace.embedding_mk_eq τ with e | e
  · have := key (InfinitePlace.mk τ) lam (by rw [e]; exact h)
    rw [e] at this
    rwa [if_pos e]
  · have := (key (InfinitePlace.mk τ) lam.dual (by rw [e]; exact h.conjugate)).conjugate
    rw [e, ComplexEmbedding.involutive_conjugate E τ] at this
    rwa [if_neg (by rw [e]; exact conjugate_ne τ)]

end AU

section Par

variable {LP : HeightOneSpectrum (𝓞 E) → Type}

end Par

section Host

open Formalism.MainNotions.N GlobalTheory.DefiniteBC

attribute [local instance] host_isCMField

variable {R : Ranks} (H : Host R)

variable {H} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

end Host

end GlobalTheory.DefU

end
