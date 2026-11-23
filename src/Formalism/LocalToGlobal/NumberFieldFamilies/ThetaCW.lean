module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCOB

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inf_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) : θ (infPart D (x : AE D)) ≠ 0 :=
  ((x.isUnit.map (infPart D)).map θ).ne_zero

theorem hasInfExp_mul {χ χ' : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a b : ℚ} (h : HasInfExp D χ τ a)
    (h' : HasInfExp D χ' τ b) : HasInfExp D (χ * χ') τ (a + b) := by
  obtain ⟨n, hn, e⟩ := h
  obtain ⟨m, hm, e'⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  have hz := inf_ne_zero (th0 D τ) x
  rw [MonoidHom.mul_apply, Circle.coe_mul, allSome_fam.1 e x h1 h2, allSome_fam.1 e' x h1 h2, zpow_add₀]
  exact div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)

theorem hasInfExp_inv {χ : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) :
    HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, e⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, allSome_fam.2 fun x h1 h2 => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, allSome_fam.1 e x h1 h2, _root_.zpow_neg]

theorem hasInfExp_one (τ : D.what₂.Tau) : HasInfExp D (1 : (AE D)ˣ →* Circle) τ 0 :=
  ⟨0, by simp, allSome_fam.2 fun x _ _ => by simp⟩


variable (D) in
def chrA : Subgroup ((AE D)ˣ →* Circle) where
  carrier := {χ | IsHeckeChar D χ ∧ ∀ τ, ∃ a, HasInfExp D χ τ a}
  one_mem' := ⟨⟨continuous_const, fun _ => rfl⟩, fun τ => ⟨0, hasInfExp_one τ⟩⟩
  mul_mem' := fun {a b} ha hb => ⟨⟨ha.1.1.mul hb.1.1, fun x => by rw [MonoidHom.mul_apply, ha.1.2, hb.1.2, one_mul]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      obtain ⟨t, ht⟩ := hb.2 τ
      exact ⟨_, hasInfExp_mul hs ht⟩⟩
  inv_mem' := fun {a} ha => ⟨⟨ha.1.1.inv, fun x => by rw [MonoidHom.inv_apply, ha.1.2, inv_one]⟩,
    fun τ => by
      obtain ⟨s, hs⟩ := ha.2 τ
      exact ⟨_, hasInfExp_inv hs⟩⟩

def ExpU (D : D7) : Prop := ∀ (χ : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D χ τ a → HasInfExp D χ τ b → a = b

theorem heis_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (f g : WA V W → ℂ) :
    Heisenberg₂ ψ V W u (f + g) = Heisenberg₂ ψ V W u f + Heisenberg₂ ψ V W u g := by
  funext w; simp [Heisenberg₂, mul_add]

theorem heis_smul (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (c : ℂ) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W u (c • f) = c • Heisenberg₂ ψ V W u f := by
  funext w
  exact mul_left_comm _ c _

def schC (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp [Heisenberg₂]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩
  add_mem' := fun {f g} hf hg => ⟨fun γ w => by rw [Pi.add_apply, Pi.add_apply, hf.quasi, hg.quasi, mul_add], by
      obtain ⟨U, hU, e⟩ := hf.level
      obtain ⟨U', hU', e'⟩ := hg.level
      exact ⟨U ⊓ U', hU.inter hU', fun u hu h0 => by rw [heis_add, e u hu.1 h0, e' u hu.2 h0]⟩,
    hf.cont.add hg.cont, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)⟩
  smul_mem' := fun c f hf => ⟨fun γ w => by
      rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm], by
      obtain ⟨U, hU, e⟩ := hf.level
      exact ⟨U, hU, fun u hu h0 => by rw [heis_smul, e u hu h0]⟩,
    hf.cont.const_smul c, fun k L h1 h2 w => (hf.smooth k L h1 h2 w).const_smul c⟩


def admitted (V W : HSp D) (χ χ' : chrA D) : Prop := ResEta D χ.1 V.rank ∧ ResEta D χ'.1 W.rank

structure IsWeil (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : chrA D)
    (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) : Prop where
  Heisenberg₂ : ∀ g h w₀ (Φ Φ' : schC ψ V W), Φ'.1 = Heisenberg₂ ψ V W w₀ Φ.1 →
    (Om (g, h) Φ').1 = Heisenberg₂ ψ V W (actHom V W g h w₀) (Om (g, h) Φ).1
  aut : ∀ γ ∈ GQ V, ∀ γ' ∈ GQ W, ∀ Φ : schC ψ V W, (Om (γ, γ') Φ).1 0 = Φ.1 0
  cont : ∀ (Φ : schC ψ V W) w, Continuous fun p : GA D V × GA D W => (Om p Φ).1 w
  unit : ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ p (Φ : schC ψ V W), ∫ w in 𝓕, ‖(Om p Φ).1 w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Φ.1 w‖ ^ 2 ∂μ
  split : ∀ e, IsSplitIdem D e → ∀ g h, SuppAt e V g → SuppAt e W h → ∀ x y, IsDetAt e V g x → IsDetAt e W h y →
    ∃ r : ℝ, 0 < r ∧ ∀ ℓ : schC ψ V W →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ' : schC ψ V W, Φ'.1 = Theta.Heisenberg₂ ψ V W u Φ.1 → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Om (g, h) Φ) = (r : ℂ) * (splitFac V W χ.1 χ'.1 x y : ℂ) * ℓ Φ
  unr : ∀ S, UnramOutside D χ.1 S → UnramOutside D χ'.1 S → ∀ k ∈ KsphC V S, ∀ k' ∈ KsphC W S, ∀ Φ : schC ψ V W,
    (∀ u ∈ latVWS V W S, Theta.Heisenberg₂ ψ V W u Φ.1 = Φ.1) → Om (k, k') Φ = Φ

def kerC {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) (Φ : schC ψ V W)
    (g : GA D V) (h : GA D W) : ℂ := (Om (g, h) Φ).1 0

def LiftOK {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} (Om : GA D V × GA D W →* Module.End ℂ (schC ψ V W)) : Prop :=
  ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ →
    ∀ (Φ : schC ψ V W) (φ : GA D V → ℂ), IsAutFunSm (th0 D) V φ → IsCuspFun V φ →
      (∀ h, IntegrableOn (fun g => kerC Om Φ g h * φ g) 𝓕 μ) ∧
      IsAutFunSm (th0 D) W fun h => ∫ g in 𝓕, kerC Om Φ g h * φ g ∂μ

structure WeilRepresentationFamily (ψ : AddChar (AF D.host.F) ℂ) where
  om : ∀ V W, chrA D → chrA D → (GA D V × GA D W →* Module.End ℂ (schC ψ V W))
  weil : ∀ V W χ χ', admitted V W χ χ' → IsWeil ψ V W χ χ' (om V W χ χ')
  twW_up : ∀ (V W : HSp D) (χ χ' ν : chrA D), V.rank ≤ W.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = (((ν.1 x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_up : ∀ (V W : HSp D) (χ χ' ν : chrA D), V.rank ≤ W.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = ((ν.1 x : Circle) : ℂ) • om V W χ χ' (g, h)
  twW_dn : ∀ (V W : HSp D) (χ χ' ν : chrA D), W.rank < V.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot V g x →
      om V W χ (χ' * ν) (g, h) = ((ν.1 x : Circle) : ℂ) • om V W χ χ' (g, h)
  twV_dn : ∀ (V W : HSp D) (χ χ' ν : chrA D), W.rank < V.rank → ResEta D χ.1 V.rank → ResEta D χ'.1 W.rank →
    ResEta D ν.1 0 → ∀ g h x, IsDetRoot W h x →
      om V W (χ * ν) χ' (g, h) = (((ν.1 x)⁻¹ : Circle) : ℂ) • om V W χ χ' (g, h)
  swap : ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → admitted V W χ χ' →
    ∀ g h (Φ : schC ψ V W) (Φ' : schC ψ W V), (∀ x : WA V W, Φ'.1 x.transpose = Φ.1 x) →
      ∀ x : WA V W, (om W V χ' χ (h, g) Φ').1 x.transpose = (om V W χ χ' (g, h) Φ).1 x

structure WeilC (ψ : AddChar (AF D.host.F) ℂ) extends WeilRepresentationFamily ψ where
  lift : ∀ V W χ χ', admitted V W χ χ' → LiftOK (om V W χ χ')

structure FormGaps (D : D7) : Prop where
  atTau : AtTauU D
  add : SmAdd D
  right : SmRight D
  conj : SmConj D
  cuspInt : CuspInt D
  volEx : VolEx D
  volU : VolU D
  petInt : PetInt D

variable {ψ : AddChar (AF D.host.F) ℂ}



open Classical in
def cptC (V : HSp D) (τ : D.what₂.Tau) :
    Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ :=
  if h : V.SigOK then (cpt_bas_ex V h τ).choose else 0

def kfinC (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (schC ψ V W) :=
  Submodule.span ℂ {Φ | IsPolFock ψ (th0 D) V W (cptC V) (cptC W) Φ.1}

end Formalism.L2.Fam.ThC

end
