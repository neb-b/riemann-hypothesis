module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

def IsHK (H : Subgroup G) (E : Set G) : Prop :=
  (∀ h ∈ H, ∀ g, h * g ∈ E ↔ g ∈ E) ∧
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, g * x ∈ E ↔ g ∈ E

theorem IsHK.compl {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsHK H Eᶜ := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  exact ⟨fun h hh g => not_congr (h1 h hh g), K, hK, fun g x hx => not_congr (h2 g x hx)⟩

theorem IsHK.inter {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∩ E') := by
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨h1', K', hK', h2'⟩ := hE'
  refine ⟨fun h hh g => and_congr (h1 h hh g) (h1' h hh g), K ⊓ K', ?_, fun g x hx =>
    and_congr (h2 g x hx.1) (h2' g x hx.2)⟩
  exact hK.inter hK'

theorem IsHK.union {H : Subgroup G} {E E' : Set G} (hE : IsHK H E) (hE' : IsHK H E') : IsHK H (E ∪ E') := by
  have := (hE.compl.inter hE'.compl).compl
  rwa [Set.compl_inter, compl_compl, compl_compl] at this

theorem IsHK.isOpen {H : Subgroup G} {E : Set G} (hE : IsHK H E) : IsOpen E := by
  obtain ⟨-, K, hK, h2⟩ := hE
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hn : (fun y => g⁻¹ * y) ⁻¹' (K : Set G) ∈ 𝓝 g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
  filter_upwards [hn] with y hy
  have e : y = g * (g⁻¹ * y) := by group
  rw [e]
  exact (h2 g _ hy).2 hg

theorem isHK_doubleCoset (H K : Subgroup G) (hK : IsOpen (K : Set G)) (c : G) :
    IsHK H {g | ∃ a ∈ H, ∃ x ∈ K, g = a * c * x} := by
  refine ⟨fun h hh g => ⟨?_, ?_⟩, K, hK, fun g y hy => ⟨?_, ?_⟩⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨h⁻¹ * a, mul_mem (inv_mem hh) ha, x, hx, by
      have e2 : g = h⁻¹ * (h * g) := by group
      rw [e2, e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨h * a, mul_mem hh ha, x, hx, by group⟩
  · rintro ⟨a, ha, x, hx, e⟩
    exact ⟨a, ha, x * y⁻¹, mul_mem hx (inv_mem hy), by
      rw [← mul_assoc, ← e]; group⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x * y, mul_mem hx hy, by group⟩

def stabSub {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem cInd_right_inv (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ ∀ g, ∀ x ∈ K, f.1.1.1 (g * x) = f.1.1.1 g := by
  refine ⟨stabSub (ind H σ) f.1.1, f.1.2, fun g x hx => ?_⟩
  have h : ind H σ x f.1.1 = f.1.1 := hx
  exact congrArg (fun v : indSpace H σ => v.1 g) h

theorem exists_indicator (H : Subgroup G) (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E)
    (f : cIndSpace H σ) :
    ∃ f' : cIndSpace H σ, (∀ g ∈ E, f'.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → f'.1.1.1 g = 0) := by
  classical
  obtain ⟨h1, K, hK, h2⟩ := hE
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H σ f
  let b : G → W := fun g => if g ∈ E then f.1.1.1 g else 0
  have hind : b ∈ indSpace H σ := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    by_cases hg : g ∈ E
    · have hg' : (h : G) * g ∈ E := (h1 h h.2 g).2 hg
      simp only [b, if_pos hg, if_pos hg', e]
    · have hg' : (h : G) * g ∉ E := fun c => hg ((h1 h h.2 g).1 c)
      simp only [b, if_neg hg, if_neg hg', map_zero]
  have hsm : (⟨b, hind⟩ : indSpace H σ) ∈ smoothPart (ind H σ) := by
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ) (K ⊓ L) (hK.inter hL) _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show b (g * x) = b g
    by_cases hg : g ∈ E
    · have hg' : g * x ∈ E := (h2 g x hx.1).2 hg
      simp only [b, if_pos hg, if_pos hg', hLi g x hx.2]
    · have hg' : g * x ∉ E := fun c => hg ((h2 g x hx.1).1 c)
      simp only [b, if_neg hg, if_neg hg']
  have hc : (⟨⟨b, hind⟩, hsm⟩ : smoothPart (ind H σ)) ∈ cIndSpace H σ := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g ?_⟩
    intro h0
    apply hg
    show b g = 0
    by_cases hgE : g ∈ E
    · simp only [b, if_pos hgE]; exact h0
    · simp only [b, if_neg hgE]
  exact ⟨⟨⟨⟨b, hind⟩, hsm⟩, hc⟩, fun g hg => if_pos hg, fun g hg => if_neg hg⟩

theorem exists_cInd_value (H : Subgroup G) (σ : Representation ℂ H W) (hσ : IsSmooth σ)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (c : G) (w : W) : ∃ e : cIndSpace H σ, e.1.1.1 c = w := by
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hσ w)
  have h1O : (1 : G) ∈ O := by
    have : (1 : H) ∈ (Subtype.val ⁻¹' O : Set H) := by rw [hOe]; simp
    exact this
  have hn : (fun x => c * x * c⁻¹) ⁻¹' O ∈ 𝓝 (1 : G) :=
    (hO.preimage (by fun_prop)).mem_nhds (by simpa using h1O)
  obtain ⟨K, hKo, hKc, hKO⟩ := hbase _ hn
  obtain ⟨B, hB, -⟩ := GlobalTheory.CompanionTheory.BZMirOnto.exists_bump H σ K hKo hKc c w (by
    intro a x hx e
    have hax : (a : G) ∈ O := by rw [e]; exact hKO hx
    have : a ∈ (Subtype.val ⁻¹' O : Set H) := hax
    rw [hOe] at this
    exact this)
  refine ⟨B, ?_⟩
  have h := hB 1 1 (one_mem K)
  simpa using h

end Abstract

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev embedding₂ (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : ((eGP m j ⟨false, a⟩ : Fin (m + j + 1)) : ℕ) = a := by
  simp [eGP, stdSum]

theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : ((eGP m j ⟨true, b⟩ : Fin (m + j + 1)) : ℕ) = m + b := by
  simp [eGP, stdSum]

theorem mem_mirabolicParabolic_iff (m j : ℕ) (g : Mir k (m + j)) :
    g ∈ MirabolicParabolic k m j ↔ ∀ (b : Fin (j + 1)) (a : Fin m),
      ((g : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)
        (eGP m j ⟨true, b⟩) (eGP m j ⟨false, a⟩) = 0 := by
  show (g : GL (Fin (m + j + 1)) k) ∈ parab k (eGP m j) ↔ _
  rw [mem_parab_iff]
  constructor
  · intro h b a
    exact h true false b a (by decide)
  · intro h x y i l hxy
    cases x <;> cases y <;> first | exact absurd hxy (by decide) | exact h i l

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n s * dpow n t := by
  ext g
  simp [dpow, Complex.ofReal_add, absPow_add]

theorem isOpen_ker_dpow (n : ℕ) (s : ℝ) :
    IsOpen (((dpow (k := k) n s).ker : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
  IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow (s : ℂ))

end Conc

end GlobalTheory.CompanionTheory.LeibPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupSmallAnnihilator
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto.PerpSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def box (m : ℕ) (s : kˣ) : AddSubgroup (Fin m → k) where
  carrier := {l | ∀ j, l j ∈ cball s}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' _ := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_box {m : ℕ} {s : kˣ} {l : Fin m → k} : l ∈ box m s ↔ ∀ j, l j ∈ cball s := by
  exact Iff.rfl

theorem coe_box (m : ℕ) (s : kˣ) :
    (box m s : Set (Fin m → k)) = Set.univ.pi fun _ => cball s := by
  ext l
  simp only [SetLike.mem_coe, mem_box, Set.mem_univ_pi]

theorem isCompact_box (m : ℕ) (s : kˣ) : IsCompact (box m s : Set (Fin m → k)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s

theorem box_mem_nhds (m : ℕ) (s : kˣ) : (box m s : Set (Fin m → k)) ∈ 𝓝 (0 : Fin m → k) := by
  rw [coe_box]
  exact set_pi_mem_nhds Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.cball_mem_nhds s

theorem exists_box_subset {m : ℕ} {Ω : Set (Fin m → k)} (hΩ : Ω ∈ 𝓝 (0 : Fin m → k)) :
    ∃ r : kˣ, (box m r : Set (Fin m → k)) ⊆ Ω := by
  rw [nhds_pi, Filter.mem_pi'] at hΩ
  obtain ⟨I, t, ht, hsub⟩ := hΩ
  choose s hs using fun i => GlobalTheory.SplitWeil.exists_cball_subset (by simpa using ht i)
  by_cases hm : Nonempty (Fin m)
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => ValuativeRel.valuation k (s i : k))
      Finset.univ_nonempty
    refine ⟨s i₀, fun l hl => hsub fun i _ => hs i ?_⟩
    exact le_trans (show ValuativeRel.valuation k (l i) ≤ _ from (mem_box.1 hl) i) (hi₀ i (Finset.mem_univ _))
  · exact ⟨1, fun l _ => hsub fun i _ => (hm ⟨i⟩).elim⟩

theorem dotProduct_mem_cball {m : ℕ} {r s : kˣ} {b l : Fin m → k} (hb : b ∈ box m (r * s⁻¹))
    (hl : l ∈ box m s) : b ⬝ᵥ l ∈ cball r := by
  unfold dotProduct
  refine Finset.sum_induction _ (· ∈ cball r) (fun a b ha hb => add_mem_cball ha hb) ?_ ?_
  · simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k 0 ≤ _
    simp
  · intro j _
    have h1 := (mem_box.1 hb) j
    have h2 := (mem_box.1 hl) j
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_ofPred_eq]
    show ValuativeRel.valuation k (b j * l j) ≤ ValuativeRel.valuation k (r : k)
    rw [map_mul]
    calc ValuativeRel.valuation k (b j) * ValuativeRel.valuation k (l j)
        ≤ ValuativeRel.valuation k ((r * s⁻¹ : kˣ) : k) * ValuativeRel.valuation k (s : k) := mul_le_mul' h1 h2
      _ = ValuativeRel.valuation k (r : k) := by
        rw [← map_mul]
        congr 1
        simp

end GlobalTheory.CompanionTheory.BZOnto.PerpSmall
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmodule
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.HwStable

variable {n : ℕ}

theorem weight_shift_real {V : Type} [AddCommGroup V] [Module ℂ V] {K : Fin n → Fin n → Module.End ℂ V}
    (hg : Formalism.REAL.GlRel K) (μ : Fin n → ℝ) {v : V}
    (hv : ∀ c, K c c v = ((μ c : ℝ) : ℂ) • v) {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    K c c (K a b v) =
      ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • K a b v := by
  have e : K c c (K a b v) = K a b (K c c v) +
      ((if c = a then K c b else 0) - (if b = c then K a c else 0)) v := by
    rw [← hg c c a b]
    simp [Module.End.mul_apply]
  rw [e, hv c, map_smul]
  by_cases h1 : c = a
  · subst h1
    have h2 : ¬ b = c := fun h => hab h.symm
    have h3 : ¬ c = b := hab
    simp only [↓reduceIte, h2, h3, LinearMap.sub_apply, LinearMap.zero_apply]
    push_cast
    module
  · by_cases h2 : c = b
    · subst h2
      simp only [↓reduceIte, h1, LinearMap.sub_apply, LinearMap.zero_apply]
      push_cast
      module
    · have h3 : ¬ b = c := fun h => h2 h.symm
      simp only [↓reduceIte, h1, h2, h3, sub_zero, LinearMap.zero_apply, add_zero]

section Main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  {G : Fin n → Fin n → Module.End ℂ H} {N : Submodule ℂ H}

def diagOn (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : Module.End ℂ N :=
  (G c c).restrict (hst c c)

theorem diagOn_symm (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (c : Fin n) : (diagOn G N hst c).IsSymmetric := by
  intro x y
  exact hs c c x.1 y.1

theorem diag_commute (hg : Formalism.REAL.GlRel G) (i j : Fin n) : Commute (G i i) (G j j) := by
  have h := hg i i j j
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · have h' : ¬ j = i := fun h => hij h.symm
    rw [if_neg hij, if_neg h', sub_zero] at h
    exact sub_eq_zero.1 h

theorem diagOn_commute (hg : Formalism.REAL.GlRel G) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) (i j : Fin n) :
    Commute (diagOn G N hst i) (diagOn G N hst j) := by
  have h : G i i * G j j = G j j * G i i := diag_commute hg i j
  show diagOn G N hst i * diagOn G N hst j = diagOn G N hst j * diagOn G N hst i
  ext x
  have := congrArg (fun f : Module.End ℂ H => f x.1) h
  simpa [diagOn, Module.End.mul_apply] using this

def wts (G : Fin n → Fin n → Module.End ℂ H) (N : Submodule ℂ H) : Set (Fin n → ℝ) :=
  {μ | ∃ v ∈ N, v ≠ 0 ∧ ∀ c, G c c v = ((μ c : ℝ) : ℂ) • v}

theorem wts_nonempty (hg : Formalism.REAL.GlRel G) (hs : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hN : N ≠ ⊥) (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Nonempty := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute (fun c => diagOn_symm hs hst c)
    (fun i j _ => diagOn_commute hg hst i j)
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin n → ℂ, (⨅ c, Module.End.eigenspace (diagOn G N hst c) (χ c)) ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    rw [iSup_congr hcon, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hev : ∀ c, diagOn G N hst c x = χ c • x := fun c =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx c)
  have hre : ∀ c, (((χ c).re : ℝ) : ℂ) = χ c := fun c => by
    have hE : Module.End.HasEigenvalue (diagOn G N hst c) (χ c) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (hev c), hx0⟩
    exact Complex.conj_eq_iff_re.1 ((diagOn_symm hs hst c).conj_eigenvalue_eq_self hE)
  refine ⟨fun c => (χ c).re, x.1, x.2, fun h => hx0 (Subtype.ext h), fun c => ?_⟩
  rw [hre c]
  exact congrArg Subtype.val (hev c)

theorem wts_finite (hst : ∀ a b, ∀ w ∈ N, G a b w ∈ N) : (wts G N).Finite := by
  have hfa : ∀ a, Set.Finite {r : ℝ | Module.End.HasEigenvalue (diagOn G N hst a) ((r : ℝ) : ℂ)} := fun a =>
    (Module.End.finite_hasEigenvalue _).preimage (Function.Injective.injOn Complex.ofReal_injective)
  refine (Set.Finite.pi' hfa).subset ?_
  rintro μ ⟨v, hv, h0, hw⟩ a
  exact Module.End.hasEigenvalue_of_hasEigenvector (x := (⟨v, hv⟩ : N))
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext (hw a)), fun h => h0 (congrArg Subtype.val h)⟩

end Main

theorem exists_highest_of_stable : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G →
    (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ →
    (∀ a b, ∀ w ∈ N, G a b w ∈ N) →
    ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  intro n H _ _ _ G hg hs N hN hst
  have hfin := wts_finite hst
  obtain ⟨μ, hμ, hmax⟩ := hfin.toFinset.exists_max_image (fun ν => toLex ν)
    (by simpa using wts_nonempty hg hs hN hst)
  obtain ⟨v, hvN, hv0, hw⟩ := hfin.mem_toFinset.1 hμ
  refine ⟨μ, v, hvN, hv0, hw, fun a b hab _ => ?_⟩
  by_contra hne
  let μ' : Fin n → ℝ := fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
  have hlt : toLex μ < toLex μ' := by
    refine ⟨a, fun j hj => ?_, ?_⟩
    · have h1 : j ≠ a := ne_of_lt hj
      have h2 : j ≠ b := ne_of_lt (lt_trans hj hab)
      show μ j = μ j + (if j = a then 1 else 0) - (if j = b then 1 else 0)
      simp [h1, h2]
    · show μ a < μ a + (if a = a then 1 else 0) - (if a = b then 1 else 0)
      simp [ne_of_lt hab]
  have hin : μ' ∈ wts G N :=
    ⟨G a b v, hst a b v hvN, hne, fun c => weight_shift_real hg μ hw (ne_of_lt hab) c⟩
  exact not_le.2 hlt (hmax μ' (hfin.mem_toFinset.2 hin))

end GlobalTheory.CompanionTheory.RealCountG.HwStable
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

section Group

variable (k : Type) [Field k]

abbrev Qp (i t : ℕ) : Subgroup (GL (Fin (i + t)) k) := parab k (two (stdSum (rfl : i + t = i + t)))

def qBlocks (i t : ℕ) : Qp k i t →* GL (Fin i) k × GL (Fin t) k :=
  MonoidHom.prod
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) false).comp (leviProj k (two (stdSum rfl))))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) true).comp (leviProj k (two (stdSum rfl))))

def uM (n : ℕ) (y : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd y), MirU_le_Mir k n ⟨_, rfl⟩⟩

def topV (i t : ℕ) (x : Fin i → k) : Fin (i + t) → k := Fin.append x 0

def midV (i t : ℕ) (v : Fin t → k) : Fin (i + t) → k := Fin.append 0 v

theorem uM_add (n : ℕ) (a b : Fin n → k) : uM k n (a + b) = uM k n a * uM k n b := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (a + b)) = unip k n (Multiplicative.ofAdd a) * unip k n (Multiplicative.ofAdd b)
  rw [ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM k n 0 = 1 := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd 0) = 1
  rw [ofAdd_zero, map_one]

theorem uM_mem (n : ℕ) (y : Fin n → k) : uM k n y ∈ MirUin k n := ⟨_, rfl⟩

theorem exists_uM_of_mem (n : ℕ) {u : Mir k n} (hu : u ∈ MirUin k n) : ∃ y, u = uM k n y := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (y : Fin n → k) :
    levi k n g * uM k n y = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec y) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd y)

theorem topV_add_midV (i t : ℕ) (x : Fin i → k) (v : Fin t → k) :
    topV k i t x + midV k i t v = Fin.append x v := by
  funext j
  induction j using Fin.addCases <;> simp [topV, midV]

theorem exists_top_mid (i t : ℕ) (y : Fin (i + t) → k) : ∃ x v, y = topV k i t x + midV k i t v := by
  refine ⟨fun j => y (Fin.castAdd t j), fun j => y (Fin.natAdd i j), ?_⟩
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def qRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Qp k i t) (Jacquet τ (MirUin k i) ⊗[ℂ] W) :=
  twist ((extTensor (psiMinus k τ) σ).comp (qBlocks k i t))
    ((detChar (Fin t) (absPow k (1 : ℂ))).comp ((MonoidHom.snd _ _).comp (qBlocks k i t)))

abbrev hRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (HPG k i t) (V ⊗[ℂ] W) :=
  (extTensor τ σ).comp (pgProj k i t)

def clT (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    V ⊗[ℂ] W →ₗ[ℂ] Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  LinearMap.rTensor W (twKer τ (MirUin k i) 1).mkQ

def evL {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W} (p : Mir k (i + t)) :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] V ⊗[ℂ] W :=
  (LinearMap.proj p) ∘ₗ (indSpace (HPG k i t) (hRep τ σ)).subtype ∘ₗ (smoothPart (ind (HPG k i t) (hRep τ σ))).subtype ∘ₗ
    (cIndSpace (HPG k i t) (hRep τ σ)).subtype

def fibV {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (v : Fin t → k) : V ⊗[ℂ] W :=
  f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g)

def fibInt {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) : Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  clT τ W (smInt μ (fibV f g))

end Rep

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

