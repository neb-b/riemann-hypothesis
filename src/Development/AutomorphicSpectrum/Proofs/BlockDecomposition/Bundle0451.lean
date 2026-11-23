module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecomp
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.HpgMem

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ)
    (h : HPG k i t), ∃ (x : Fin i → k) (q : Qp k i t),
      (h : Mir k (i + t)) = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) := by
  intro k _ _ _ _ i t h
  set M : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k :=
    (((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) with hM
  have hmem : ((h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈
      GlobalTheory.SmGL.parab k (GlobalTheory.BZMir.Leib.ePG i t) := h.2
  have hp := GlobalTheory.SmGL.mem_parab_iff.1 hmem
  have hp' : ∀ (a : Fin t) (b : Fin (i + 1)),
      M (GlobalTheory.BZMir.Leib.ePG i t ⟨true, a⟩) (GlobalTheory.BZMir.Leib.ePG i t ⟨false, b⟩) = 0 :=
    fun a b => hp true false a b (by decide)
  have hzero : ∀ (r : Fin t) (c : Fin i),
      M (Fin.castSucc (Fin.natAdd i r)) (Fin.castSucc (Fin.castAdd t c)) = 0 := by
    intro r c
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    have h₂ : Fin.castSucc (Fin.castAdd t c) =
        GlobalTheory.BZMir.Leib.ePG i t ⟨false, Fin.castSucc c⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_false_val, Fin.coe_castAdd])
    rw [h₁, h₂]
    exact hp' r (Fin.castSucc c)
  have hlast : ∀ r : Fin t, M (Fin.castSucc (Fin.natAdd i r)) (Fin.last (i + t)) = 0 := by
    intro r
    have h₁ : Fin.castSucc (Fin.natAdd i r) = GlobalTheory.BZMir.Leib.ePG i t ⟨true, r⟩ :=
      Fin.ext (by rw [Fin.coe_castSucc, GlobalTheory.CompanionTheory.BZPhiPG.Cells.ePG_true_val, Fin.coe_natAdd])
    rw [h₁, ← GlobalTheory.BZMir.Leib.ePG_false_last i t]
    exact hp' r (Fin.last i)
  have hgen : ∀ (r : Fin t) (c : Fin i) (x y : Fin (i + t)), (x : ℕ) = i + r → (y : ℕ) = c →
      ((GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) : GL (Fin (i + t)) k) :
        Matrix (Fin (i + t)) (Fin (i + t)) k) x y = 0 := by
    intro r c x y hx hy
    have hx' : x = Fin.natAdd i r := Fin.ext (by rw [hx, Fin.coe_natAdd])
    have hy' : y = Fin.castAdd t c := Fin.ext (by rw [hy, Fin.coe_castAdd])
    subst hx' hy'
    exact hzero r c
  have hq : GlobalTheory.BZMir.mirabolicProjection k (i + t) (h : GlobalTheory.BZMir.Mir k (i + t)) ∈
      GlobalTheory.CompanionTheory.BZPsiPG.Qp k i t := by
    unfold GlobalTheory.CompanionTheory.BZPsiPG.Qp
    rw [GlobalTheory.SmGL.mem_parab_iff]
    intro a b ia jb hab
    cases a <;> cases b
    · exact absurd hab (by decide)
    · exact absurd hab (by decide)
    · refine hgen ia jb _ _ ?_ ?_
      · rfl
      · rfl
    · exact absurd hab (by decide)
  obtain ⟨x, hx⟩ : ∃ x : Fin i → k, x = fun a => M (Fin.castSucc (Fin.castAdd t a)) (Fin.last (i + t)) :=
    ⟨_, rfl⟩
  have hv : (fun r : Fin (i + t) => M (Fin.castSucc r) (Fin.last (i + t))) = GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x := by
    funext r
    cases r using Fin.addCases with
    | left a => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_left, hx]
    | right b => rw [GlobalTheory.CompanionTheory.BZPsiPG.topV, Fin.append_right, Pi.zero_apply]; exact hlast b
  refine ⟨x, ⟨_, hq⟩, ?_⟩
  apply Subtype.ext
  have hd : ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k) =
      unip k (i + t) (Multiplicative.ofAdd fun r => M (Fin.castSucc r) (Fin.last (i + t))) *
        glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))) := by
    have hh := (mem_Mir_iff k ((h : Mir k (i + t)) : GL (Fin (i + t + 1)) k)).1 (h : Mir k (i + t)).2
    ext1
    rw [Units.val_mul]
    show _ = (1 + colMat k (i + t) _) * glEmbMat k (i + t) (blockMat k (i + t) _)
    rw [add_mul, one_mul, colMat_mul_glEmbMat]
    ext a b
    induction a using Fin.lastCases with
    | last =>
      rw [hh]
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, eLast, Fin.castSucc_ne_last, Pi.single_apply]
    | cast a =>
      induction b using Fin.lastCases <;>
        simp [glEmbMat, colMat, blockMat, Fin.castSucc_ne_last, M]
  refine hd.trans ?_
  exact congrArg (· * glEmb k (i + t) (mirabolicProjection k (i + t) (h : Mir k (i + t))))
    (congrArg (fun w => unip k (i + t) (Multiplicative.ofAdd w)) hv)

end GlobalTheory.CompanionTheory.BZPsiPG.HpgMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPreservesIsomorphism
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

section twEquiv
variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nonempty_twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  have hl : ∀ v, e.toIntertwiningMap.toLinearMap v = e v := fun v => rfl
  have hmap : (GlobalTheory.PRep.twKer ρ N θ).map (e.toLinearEquiv : V →ₗ[ℂ] W) = GlobalTheory.PRep.twKer σ N θ := by
    unfold GlobalTheory.PRep.twKer
    rw [Submodule.map_span]
    congr 1
    ext w
    constructor
    · rintro ⟨x, ⟨n, v, rfl⟩, rfl⟩
      refine ⟨n, e v, ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint]
    · rintro ⟨n, w', rfl⟩
      refine ⟨ρ n (e.toLinearEquiv.symm w') - ((θ n : ℂˣ) : ℂ) • e.toLinearEquiv.symm w', ⟨n, _, rfl⟩, ?_⟩
      have hw : e (e.toLinearEquiv.symm w') = w' := e.toLinearEquiv.apply_symm_apply w'
      simp only [LinearEquiv.coe_coe, map_sub, map_smul, he, hl, eint, hw]
  refine ⟨Representation.Equiv.mk (Submodule.Quotient.equiv _ _ e.toLinearEquiv hmap) fun m => ?_⟩
  apply Submodule.linearMap_qext
  ext v
  exact congrArg (Submodule.Quotient.mk (p := GlobalTheory.PRep.twKer σ N θ)) (eint e (s m) v)

theorem nonempty_twist_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (χ : G →* ℂˣ) :
    Nonempty ((twist ρ χ).Equiv (twist σ χ)) := by
  have he : ∀ v, e.toLinearEquiv v = e v := fun v => rfl
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  show e.toLinearEquiv (((χ g : ℂˣ) : ℂ) • ρ g v) = ((χ g : ℂˣ) : ℂ) • σ g (e.toLinearEquiv v)
  rw [map_smul, he, he, eint]

end twEquiv

theorem miso_phiN (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (A B : MRep k (n + 1)) (h : MIso A B) : MIso (phiN ψ A) (phiN ψ B) := by
  have h1 : MIso (GlobalTheory.BZMir.MRep.phiM k ψ A) (GlobalTheory.BZMir.MRep.phiM k ψ B) := by
    obtain ⟨e⟩ := h
    unfold GlobalTheory.BZMir.MRep.phiM GlobalTheory.BZMir.phiMinus
    exact nonempty_twAct_equiv e _ _ _ (levi_stab ψ n)
  obtain ⟨e'⟩ := h1
  exact nonempty_twist_equiv e' _

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiProductRankZeroTrivial
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.PhiGpZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mir_zero_eq_one (p : Mir k 0) : p = 1 := by
  have hp := (mem_Mir_iff k (p : GL (Fin 1) k)).1 p.2
  apply Subtype.ext
  apply Units.ext
  ext a b
  obtain rfl : a = Fin.last 0 := Fin.ext (by simp)
  obtain rfl : b = Fin.last 0 := Fin.ext (by simp)
  have := congrFun hp (Fin.last 0)
  simpa [eLast] using this

theorem mirProj_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [GlobalTheory.CompanionTheory.GpUnip.mirUin_entry k n u hu _ _ (Fin.castSucc_ne_last b)]
  simp [Matrix.one_apply, Fin.castSucc_inj]

theorem conj_mem (n : ℕ) (g u : Mir k n) (hu : u ∈ MirUin k n) : g * u * g⁻¹ ∈ MirUin k n := by
  apply GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, mirProj_of_mem n u hu, mul_one, map_inv, mul_inv_cancel]

theorem mem_mirabolicParabolic_zero (m : ℕ) (g : Mir k (m + 1 + 0)) : g ∈ MirabolicParabolic k (m + 1) 0 := by
  rw [GlobalTheory.CompanionTheory.GPMem.mem_mirabolicParabolic_iff_mirabolicProj_mem_parabolic, mem_parab_two]
  intro b
  exact b.elim0

theorem cInd_apply_of_conj {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (u : G)
    (hu : ∀ g : G, ∃ h : g * u * g⁻¹ ∈ H, σ ⟨_, h⟩ = 1) (f : cIndSpace H σ) : cInd H σ u f = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  show f.1.1.1 (g * u) = f.1.1.1 g
  obtain ⟨h, hσ⟩ := hu g
  have hf : f.1.1.1 (g * u * g⁻¹ * g) = σ ⟨_, h⟩ (f.1.1.1 g) := f.1.1.2 ⟨_, h⟩ g
  have e : (g * u * g⁻¹) * g = g * u := by group
  rw [e, hσ] at hf
  exact hf

theorem prodGP_unipotent_apply {m : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ₁ : Representation ℂ (GL (Fin (m + 1)) k) V) (τ₁ : Representation ℂ (Mir k 0) W)
    (u : Mir k (m + 1 + 0)) (hu : u ∈ MirUin k (m + 1 + 0))
    (f : cIndSpace (MirabolicParabolic k (m + 1) 0) ((extTensor ρ₁ τ₁).comp (gpProj k (m + 1) 0))) :
    prodGP ρ₁ τ₁ u f = f := by
  refine cInd_apply_of_conj _ _ u (fun g => ⟨mem_mirabolicParabolic_zero m _, ?_⟩) f
  have hc := conj_mem (m + 1 + 0) g u hu
  have hp : gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩ = 1 :=
    Prod.ext (GlobalTheory.CompanionTheory.GpUnip.gpProj_unip k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m _⟩ hc).1 (mir_zero_eq_one _)
  show (extTensor ρ₁ τ₁) (gpProj k (m + 1) 0 ⟨_, mem_mirabolicParabolic_zero m (g * u * g⁻¹)⟩) = 1
  rw [hp, map_one]

theorem exists_mirChar_ne (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ) :
    ∃ u : MirUin k (n + 1), mirChar k ψ n u ≠ 1 := by
  obtain ⟨x, hx⟩ := (AddChar.ne_one_iff).1 hψ
  let w : Multiplicative (Fin (n + 1) → k) := Multiplicative.ofAdd (Pi.single (Fin.last n) x)
  let u : MirUin k (n + 1) := ⟨⟨unip k (n + 1) w, MirU_le_Mir k (n + 1) ⟨w, rfl⟩⟩, ⟨w, rfl⟩⟩
  refine ⟨u, ?_⟩
  rw [mirChar_eq k ψ n u w rfl]
  intro h
  apply hx
  have h2 : Circle.toUnits (ψ x) = 1 := by simpa [w] using h
  have h3 : ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) = 1 := by rw [h2]; rfl
  exact Circle.ext (by simpa using h3)

theorem phiN_subsingleton_of_fixed (ψ : AddChar k Circle) {n : ℕ} (X : MRep k (n + 1)) (u : MirUin k (n + 1))
    (hθ : mirChar k ψ n u ≠ 1) (hu : ∀ v, X.ρ (u : Mir k (n + 1)) v = v) : Subsingleton (phiN ψ X).V := by
  have hne : (1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ) ≠ 0 := by
    intro h
    apply hθ
    apply Units.ext
    rw [Units.val_one]
    exact (sub_eq_zero.1 h).symm
  have top : twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hmem : X.ρ (u : Mir k (n + 1)) v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v ∈
        twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n) := Submodule.subset_span ⟨u, v, rfl⟩
    rw [hu] at hmem
    have e : v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ))⁻¹ • (v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v) := by
      conv_rhs => rw [show v - ((mirChar k ψ n u : ℂˣ) : ℂ) • v = ((1 : ℂ) - ((mirChar k ψ n u : ℂˣ) : ℂ)) • v by
        rw [sub_smul, one_smul]]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  show Subsingleton (X.V ⧸ twKer X.ρ (MirUin k (n + 1)) (mirChar k ψ n))
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => exact (Submodule.Quotient.eq _).2 (top ▸ Submodule.mem_top)

theorem phiN_prodGPn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (ρ : GRep k (m + 1)) (τ : MRep k 0)
    (h : (m + 1) + 0 = (m + 0) + 1), IsSmooth ρ.ρ → IsSmooth τ.ρ →
    Subsingleton (phiN ψ (mcast h (prodGPn ρ τ))).V := by
  intro k _ _ _ _ ψ _ hψ m ρ τ h _ _
  obtain ⟨u, hu⟩ := exists_mirChar_ne ψ hψ (m + 0)
  refine phiN_subsingleton_of_fixed ψ (mcast h (prodGPn ρ τ)) u hu ?_
  intro v
  exact prodGP_unipotent_apply _ _ _ u.2 v

end GlobalTheory.CompanionTheory.PhiGpZero

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiPreservesIsomorphism
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.PsiIso

private theorem mapQ_eq_id_of_eq_id {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : Submodule R M) {f : M →ₗ[R] M} (hf : f = LinearMap.id) (h : p ≤ p.comap f) :
    p.mapQ p f h = LinearMap.id := by
  subst hf
  exact Submodule.mapQ_id p h

private theorem mapQ_congr {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
    [Module R M₂] (p : Submodule R M) (q : Submodule R M₂) {f g : M →ₗ[R] M₂} (hfg : f = g)
    (hf : p ≤ q.comap f) (hg : p ≤ q.comap g) : p.mapQ q f hf = p.mapQ q g hg := by
  subst hfg
  rfl

theorem twAct_equiv {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let eL : V ≃ₗ[ℂ] W :=
    { e.toIntertwiningMap.toLinearMap with
      invFun := e.invFun
      left_inv := e.left_inv
      right_inv := e.right_inv }
  have hf : ∀ (g : G) (v : V), (eL : V →ₗ[ℂ] W) (ρ g v) = σ g ((eL : V →ₗ[ℂ] W) v) :=
    fun g v => Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  have hg : ∀ (g : G) (w : W), (eL.symm : W →ₗ[ℂ] V) (σ g w) = ρ g ((eL.symm : W →ₗ[ℂ] V) w) := by
    intro g w
    apply eL.injective
    have := hf g (eL.symm w)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    exact this.symm
  have hf' : ∀ (g : G) (v : V), eL (ρ g v) = σ g (eL v) := hf
  have hfc : ∀ g : G, (eL : V →ₗ[ℂ] W) ∘ₗ ρ g = σ g ∘ₗ (eL : V →ₗ[ℂ] W) :=
    fun g => LinearMap.ext fun v => hf g v
  let F := GlobalTheory.BZMir.twMap ρ σ N θ (eL : V →ₗ[ℂ] W) hf
  let F' := GlobalTheory.BZMir.twMap σ ρ N θ (eL.symm : W →ₗ[ℂ] V) hg
  have hF'F : F' ∘ₗ F = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext v
    simp
  have hFF' : F ∘ₗ F' = LinearMap.id := by
    simp only [F, F', GlobalTheory.BZMir.twMap]
    rw [← Submodule.mapQ_comp]
    refine mapQ_eq_id_of_eq_id _ ?_ _
    ext w
    simp
  have hcomm : ∀ m : M, F ∘ₗ GlobalTheory.BZMir.twAct ρ N θ s hs m =
      GlobalTheory.BZMir.twAct σ N θ s hs m ∘ₗ F := by
    intro m
    first
      | (simp only [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct,
            MonoidHom.coe_mk, OneHom.coe_mk]
         erw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
         exact mapQ_congr _ _ (hfc (s m)) _ _)
      | (apply Submodule.linearMap_qext
         ext v
         simp [F, GlobalTheory.BZMir.twMap, GlobalTheory.BZMir.twAct, hf, hf'])
  exact ⟨⟨⟨F, hcomm⟩, F', fun x => LinearMap.congr_fun hF'F x, fun y => LinearMap.congr_fun hFF' y⟩⟩

theorem giso_psiN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (A B : MRep k n), MIso A B → GIso (psiN A) (psiN B) := by
  intro k _ _ _ _ n A B ⟨e⟩
  exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw _
    (GlobalTheory.CompanionTheory.LeibOrd.PsiIso.twAct_equiv e (GlobalTheory.BZMir.MirUin k n) 1
      (GlobalTheory.BZMir.levi k n) (GlobalTheory.BZMir.levi_normalises n))

end GlobalTheory.CompanionTheory.LeibOrd.PsiIso

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeLowerBlockAtOne
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativePreservesEquivariant
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inv_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (m : ℕ) (g : GL (Fin m) k) (M : Set (Fin m → k))
    (F : (Fin m → k) → ℂ) :
    ∫ x in M, F (((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x) ∂(piHaar ν m) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
        ∫ y in {y | (g : Matrix (Fin m) (Fin m) k) *ᵥ y ∈ M}, F y ∂(piHaar ν m) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hinv : ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) * (g : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.inv_mul g
  have hinv' : (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.mul_inv g
  let e : (Fin m → k) ≃ᵐ (Fin m → k) :=
    { toFun := fun x => (g : Matrix (Fin m) (Fin m) k) *ᵥ x
      invFun := fun x => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x
      left_inv := fun x => by simp only [mulVec_mulVec, hinv, one_mulVec]
      right_inv := fun x => by simp only [mulVec_mulVec, hinv', one_mulVec]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have he : MeasurableEmbedding (Matrix.mulVec (g : Matrix (Fin m) (Fin m) k)) :=
    e.measurableEmbedding
  have hμ := GlobalTheory.UnipChange.smul_map_mulVec_pi ν (g : Matrix (Fin m) (Fin m) k)
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.val_det_apply g)
  unfold GlobalTheory.CompanionTheory.MirPair.piHaar GlobalTheory.SplitWeil.nabs
  conv_lhs => rw [← hμ]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul,
    he.restrict_map, he.integral_map]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mulVec_mulVec, hinv, one_mulVec]

end GlobalTheory.CompanionTheory.MirPair
end

