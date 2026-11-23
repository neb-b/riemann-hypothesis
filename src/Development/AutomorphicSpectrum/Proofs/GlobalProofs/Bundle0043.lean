module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.CuspEmbed

def piTensorMap {α : Type} {Γ Y Z : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) : (piTensor ρ).IntertwiningMap (piTensor σ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact (f a).isIntertwining _ _ _ _

theorem piTensorMap_injective {α : Type} [Fintype α] [DecidableEq α] {Γ Y Z : α → Type}
    [∀ a, Group (Γ a)] [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    {ρ : ∀ a, Representation ℂ (Γ a) (Y a)} {σ : ∀ a, Representation ℂ (Γ a) (Z a)}
    (f : ∀ a, (ρ a).IntertwiningMap (σ a)) (hf : ∀ a, Function.Injective (f a)) :
    Function.Injective (piTensorMap f) :=
  GlobalTheory.CompanionTheory.PiTensor.map_injective_of_injective ℂ α Y Z (fun a => (f a).toLinearMap) hf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_injective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {σ : Representation ℂ (Levi k m) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f) :
    Function.Injective (parIndMap e f) := fun x y h =>
  Subtype.ext (Subtype.ext (funext fun g => hf
    (congrArg (fun z : IndSp e σ => z.1.1 g) h)))

def Embeds (N : ℕ) (Q : Irr k N) : Prop :=
  ∃ (s : ℕ) (u : Fin s → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
    (∀ a, (u a).IsCusp) ∧ ∃ φ : Q.π.IntertwiningMap (multiProd e fun a => (u a).rep),
      Function.Injective φ

theorem intertw_of_subsingleton {G V W : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (f : V →ₗ[ℂ] W)
    (g : G) : f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

theorem embeds_zero (Q : Irr k 0) : Embeds 0 Q := by
  have hQ := Q.irr
  have := nontrivial_of_irreducible hQ
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Q.V)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ Q.V, f v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hker : Function.Injective f := by
    let S : Subrepresentation Q.π := ⟨LinearMap.ker f, fun g x hx => by
      rw [Subsingleton.elim g 1, map_one]
      exact hx⟩
    rcases eq_bot_or_eq_top S with h | h
    · have h' : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 h'
    · have h' : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd (LinearMap.ker_eq_top.1 h' ▸ rfl : f v = 0) hf
  let u : Fin 0 → IrrGL (k := k) := fun a => a.elim0
  haveI : IsEmpty (Σ a, Fin (u a).1) := ⟨fun x => x.1.elim0⟩
  let e : (Σ a, Fin (u a).1) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  let L := GlobalTheory.EmptyProd.lineEquiv (k := k) e fun a => (u a).rep
  exact ⟨0, u, e, fun a => a.elim0,
    ⟨L.symm.toLinearMap ∘ₗ f, intertw_of_subsingleton _ _ _⟩, L.symm.injective.comp hker⟩

theorem embeds_cusp (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) : Embeds n π := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  let x : IrrGL (k := k) := IrrGL.of π.π π.smooth π.irr
  let ψ := multiProdEquiv e fun _ : Fin 1 => IrrGL.equivOf π.π π.smooth π.irr
  refine ⟨1, fun _ => x, e, fun _ => (IrrGL.isCusp_of.2 ⟨hn, hc⟩), (φ.trans ψ).toIntertwiningMap,
    (φ.trans ψ).toLinearEquiv.injective⟩

theorem reduce_embed (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hGL : GlobalTheory.Published.GeometricLemma) (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ ∃ φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π),
        Function.Injective φ := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := GlobalTheory.CuspSupportExist.L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := GlobalTheory.CuspSupportExist.L_tens hGL k n π s d e Y τ hτi hτq
  have hirr : (piTensor fun a => (σ a).π).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin s) (fun a => Fin (d a)) fun a => (σ a).toIrrRep
  obtain ⟨ε⟩ := hσ.nonempty_equiv hτi hirr
  let ψ := parIndEquiv e ε.symm
  exact ⟨s, d, e, σ, GlobalTheory.CuspSupportExist.L_lt k n s d e hne,
    ψ.toIntertwiningMap.comp φ, ψ.toLinearEquiv.injective.comp hφ⟩

theorem glue_embed (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (φ : π.π.IntertwiningMap (multiProd e fun a => (σ a).π))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k))
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a)) (hu : ∀ a b, (u a b).IsCusp)
    (ψ : ∀ a, (σ a).π.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) : Embeds n π := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := _root_.GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (_root_.GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (piTensorMap ψ)
  have hΨ : Function.Injective Ψ := parIndMap_injective e _ (piTensorMap_injective ψ hψ)
  exact ⟨∑ a, t a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    fun c => hu _ _, (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ)⟩

theorem embeds (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma)
    (N : ℕ) (Q : Irr k N) : Embeds N Q := by
  induction N using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact embeds_zero Q
  by_cases hc : IsCuspidal Q.π
  · exact embeds_cusp n hn Q hc
  · have hr := reduce_embed hBZ hGL n Q hc
    obtain ⟨s, d, e, σ, hlt, hr⟩ := hr
    obtain ⟨φ, hφ⟩ := hr
    have h : ∀ a, Embeds (d a) (σ a) := fun a => ih (d a) (hlt a) (σ a)
    unfold Embeds at h
    choose t u e' hu ψ hψ using h
    exact glue_embed n Q s d e σ φ hφ t u e' hu ψ hψ

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (Q : GlobalTheory.SplitRead.Irr k N),
      ∃ (s : ℕ) (u : Fin s → GlobalTheory.LocGL.IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin N),
        (∀ a, (u a).IsCusp) ∧
          ∃ φ : Q.π.IntertwiningMap (GlobalTheory.SmGL.multiProd e fun a => (u a).rep),
            Function.Injective φ :=
  fun hBZ hGL _ _ _ _ _ N Q => embeds hBZ hGL N Q

end GlobalTheory.CompanionTheory.CuspEmbed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.StabOfFrame
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodPos

theorem stab_of_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (w : InfinitePlace F) (cw : GL (Fin n) (w.Completion ⊗[F] E)),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) cw.1 * JR w.Completion J * cw.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (l d : ℕ) (h : l + d ≤ r),
      ∃ (u : GArch σ J w) (N : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E)),
        (matHom _ σ J u).1 * Xf.map (inclR (F := F) w.Completion) =
          Xf.map (inclR (F := F) w.Completion) + Xf.map (inclR (F := F) w.Completion) * N ∧
        (∀ i j, N i j ≠ 0 → (i.val < l ∧ l ≤ j.val) ∨ (i.val < l + d ∧ l + d ≤ j.val)) ∧
        (∀ v : Fin n → w.Completion ⊗[F] E,
          (∀ i : Fin r, i.val < l + d →
            Matrix.mulVec ((Formalism.UG.cT (σ : E →+* E) Xf * J).map (inclR (F := F) w.Completion)) v i = 0) →
          ∃ a : Fin r → w.Completion ⊗[F] E, (∀ i, a i ≠ 0 → i.val < l + d) ∧
            Matrix.mulVec (matHom _ σ J u).1 v - v = Matrix.mulVec (Xf.map (inclR (F := F) w.Completion)) a) ∧
        ∃ y₀ : GL (Fin d) (w.Completion ⊗[F] E), ∀ k : GL (Fin d) (w.Completion ⊗[F] E),
          Formalism.UG.cT (sigR w.Completion σ) k.1 * k.1 = 1 → ∀ g : GArch σ J w,
          (matHom _ σ J g).1 = 1 + (GlobalTheory.BlockForms.blkCols h Xf).map (inclR (F := F) w.Completion) * ((y₀ * k * y₀⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J).map (inclR (F := F) w.Completion) +
          (GlobalTheory.BlockForms.blkCols h Yf).map (inclR (F := F) w.Completion) * (Formalism.UG.cT (sigR w.Completion σ) ((y₀ * k * y₀⁻¹)⁻¹).1 - 1) *
            (Formalism.UG.cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J).map (inclR (F := F) w.Completion) →
          u * g * u⁻¹ ∈ stabArch σ J w cw := by
  intro F E _ _ _ _ _ σ hcm n J hJ r Xf Yf hW w cw hcw l d h
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  obtain ⟨ε, hε⟩ := hcw
  have hbij := infEmb_bijective hcm τ
  let φ : w.Completion ⊗[F] E →+* ℂ := infEmb τ
  let e : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective φ hbij
  have hsymm : ∀ z, φ (e.symm z) = z := e.apply_symm_apply
  have hinj : ∀ {a b : ℕ} {P Q : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)}, P.map φ = Q.map φ → P = Q :=
    fun hPQ => Matrix.map_injective hbij.1 hPQ
  have hincl : ∀ x : E, φ (inclR (F := F) w.Completion x) = τ.1 x := by
    intro x
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] x) = _
    simp
  have hinclM : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Z.map (inclR (F := F) w.Completion)).map φ = Z.map τ.1 := by
    intro a b Z; ext i j; exact hincl _
  have hcTE : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), (Formalism.UG.cT (σ : E →+* E) Z).map τ.1 = (Z.map τ.1).conjTranspose := by
    intro a b Z; ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hcm.2.2.2]
  have hcTR : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (w.Completion ⊗[F] E)),
      (Formalism.UG.cT (sigR w.Completion σ) Z).map φ = (Z.map φ).conjTranspose := by
    intro a b Z; ext i j; exact (infEmb_sigR hcm τ _).symm
  have hbcb : ∀ {m : ℕ} (a : GL (Fin m) ℂ), Formalism.UG.bc φ (Formalism.UG.bc e.symm.toRingHom a) = a := by
    intro m a; ext i j; exact hsymm _
  have hJR : (JR w.Completion J).map φ = J.map τ.1 := hinclM J

  have hJ' : (J.map τ.1).conjTranspose = J.map τ.1 := by
    rw [← hcTE]; congr 1; ext i j; exact hJ.1 i j
  have hxx : (Xf.map τ.1).conjTranspose * J.map τ.1 * Xf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  have hyy : (Yf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 0 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  have hxy : (Xf.map τ.1).conjTranspose * J.map τ.1 * Yf.map τ.1 = 1 := by
    rw [← hcTE, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc' : (Formalism.UG.bc φ cw).1.conjTranspose * J.map τ.1 * (Formalism.UG.bc φ cw).1 =
      Matrix.diagonal (fun i => if ε i then 1 else -1) := by
    have := congrArg (fun P => P.map φ) hε
    simp only [Matrix.map_mul, hcTR, hJR, Matrix.diagonal_map (map_zero _)] at this
    change (cw.1.map φ).conjTranspose * _ * cw.1.map φ = _
    rw [this]; congr 1; funext i; split_ifs <;> simp
  obtain ⟨u, N, hu, huXN, hNX, hNv, y₀, hy⟩ := GlobalTheory.MajPosCpx.exists_unip_conj_unitary n r (J.map τ.1) hJ' (Xf.map τ.1) (Yf.map τ.1) hxx hyy hxy
    (Formalism.UG.bc φ cw) ε hc' l d h

  let u0 : GL (Fin n) (w.Completion ⊗[F] E) := Formalism.UG.bc e.symm.toRingHom u
  have hu0 : u0.1.map φ = u.1 := congrArg Units.val (hbcb u)
  have hmem : u0 ∈ HR w.Completion σ J := by
    change Formalism.UG.cT (sigR w.Completion σ) u0.1 * JR w.Completion J * u0.1 = JR w.Completion J
    apply hinj
    rw [Matrix.map_mul, Matrix.map_mul, hcTR, hu0, hJR]
    exact hu
  let uA : GArch σ J w := (⟨u0, hmem⟩ : HR w.Completion σ J)
  have huA : (matHom _ σ J uA) = u0 := rfl
  let N0 : Matrix (Fin r) (Fin r) (w.Completion ⊗[F] E) := N.map e.symm
  have hN0 : N0.map φ = N := by ext i j; exact hsymm _
  refine ⟨uA, N0, ?_, ?_, ?_, Formalism.UG.bc e.symm.toRingHom y₀, ?_⟩
  · rw [huA]
    apply hinj
    rw [Matrix.map_mul, Matrix.map_add φ (map_add φ), Matrix.map_mul, hN0, hinclM, hu0]
    exact huXN
  · intro i j hne
    refine hNX i j ?_
    intro h0
    apply hne
    have : φ (N0 i j) = N i j := hsymm _
    rw [h0] at this
    exact hbij.1 (this.trans (map_zero φ).symm)
  · intro v hv
    have hv' : ∀ i : Fin r, i.val < l + d → Matrix.mulVec ((Xf.map τ.1).conjTranspose * J.map τ.1) (φ ∘ v) i = 0 := by
      intro i hi
      have := congrArg φ (hv i hi)
      rw [RingHom.map_mulVec, hinclM, Matrix.map_mul, hcTE, map_zero] at this
      exact this
    obtain ⟨a', ha', hav⟩ := hNv (φ ∘ v) hv'
    refine ⟨e.symm ∘ a', fun i hi => ha' i fun h0 => hi ?_, ?_⟩
    · show e.symm (a' i) = 0
      rw [h0, map_zero]
    · rw [huA]
      funext i
      apply hbij.1
      have hφa : φ ∘ (e.symm ∘ a') = a' := funext fun i => hsymm _
      rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, RingHom.map_mulVec, hinclM, hφa]
      have h2 := congrFun hav i
      rw [Pi.sub_apply] at h2
      have h3 : (u0.1.map φ) = u.1 := hu0
      rw [h3]
      exact h2
  · intro k hk g hg
    have hval : ∀ {m : ℕ} (a : GL (Fin m) (w.Completion ⊗[F] E)), a.1.map φ = (Formalism.UG.bc φ a).1 := fun a => rfl
    have hk' : (Formalism.UG.bc φ k).1.conjTranspose * (Formalism.UG.bc φ k).1 = 1 := by
      have := congrArg (fun P => P.map φ) hk
      simpa only [Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), hval] using this
    have hM := hy (Formalism.UG.bc φ k) hk'
    have hgφ : (matHom _ σ J g).1.map φ = 1 + ((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        ((y₀ * Formalism.UG.bc φ k * y₀⁻¹).1 - 1) *
        (((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) +
        ((Yf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) *
        (((y₀ * Formalism.UG.bc φ k * y₀⁻¹)⁻¹).1.conjTranspose - 1) *
        (((Xf.map τ.1).submatrix id fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)).conjTranspose * J.map τ.1) := by
      rw [hg]
      simp only [Matrix.map_add φ (map_add φ), Matrix.map_sub φ (map_sub φ), Matrix.map_mul, Matrix.map_one φ (map_zero φ) (map_one φ),
        hinclM, hcTE, hcTR, hval, map_mul, map_inv, hbcb]
      rfl
    have hbu : Formalism.UG.bc φ u0 = u := hbcb u
    have hmain : (cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw).1.map φ =
        ((Formalism.UG.bc φ cw)⁻¹).1 * u.1 * (matHom _ σ J g).1.map φ * (u⁻¹).1 * (Formalism.UG.bc φ cw).1 := by
      rw [hval]
      simp only [map_mul, map_inv, huA, hbu, Units.val_mul, mul_assoc]
      rfl
    rw [mem_stabArch]
    generalize hx : cw⁻¹ * matHom _ σ J (uA * g * uA⁻¹) * cw = x
    change Formalism.UG.cT _ x.1 * 1 * x.1 = 1
    apply hinj
    rw [mul_one, Matrix.map_mul, hcTR, Matrix.map_one _ (map_zero _) (map_one _), ← hx, hmain, hgφ]
    exact hM

end GlobalTheory.CompanionTheory.GoodPos
end
end

