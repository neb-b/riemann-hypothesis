module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle0002
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuGalSquare

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : τb.comp τa = τd.comp τc) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI t₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI t₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨hτ.symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem commute_phi_gal (σ : Gal(PadicAlgCl l/K)) : Commute (ACris.phi (K := ℂ_[l]) (p := l)) (ACris.galCris σ) :=
  RingHom.ext fun a => ACris.phi_gal_smul σ a

theorem phiA_comp_gal (σ : Gal(PadicAlgCl l/K)) (N : ℕ) :
    (Mid.phiA l N).comp (ACris.galCris σ) = (ACris.galCris σ).comp (Mid.phiA l N) :=
  ((commute_phi_gal σ).pow_left N).eq

theorem commute_phi_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Commute ((base l).phi n) (galBase σ n) :=
  RingHom.ext fun r => by
    obtain ⟨a, rfl⟩ := (RL.base_acr (base l) isBase_base).2 n |>.1 r
    change (base l).phi n (galBase σ n ((base l).cris n a)) = galBase σ n ((base l).phi n ((base l).cris n a))
    rw [galBase_cris, (base l).phi_cris, (base l).phi_cris, galBase_cris]
    exact congrArg _ (ACris.phi_gal_smul σ a)

theorem phiP_galBase (σ : Gal(PadicAlgCl l/K)) (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N (galBase σ n x) = galBase σ n (Mid.phiP l n N x) :=
  RingHom.congr_fun ((commute_phi_galBase σ n).pow_left N).eq x

theorem nu_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  intro l _ K r N hT M σ hσ n j x
  exact cr_square_semi
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (Mid.mOut r M n hT) (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) (galBase_cris σ n)
    (phiA_comp_gal σ N) (phiP_galBase σ n N) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuGalSquare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuPullbackCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuPull

theorem nu_pull {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (n j : ℕ)
    (x : B.Hc (B.schFn M'.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.pullHc (okToOC l K) (B.schMap u hu) true n j x) = pullM r u hu n j (Mid.nu r M' n j hT x) := by
  unfold Mid.nu pullM B.pullHc Mid.nuMor pullT' B.pullMorC
  exact (cr_square (Mid.mOut r M' n hT)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M'.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism ((B.schMap u hu).ptK _) fun _ _ _ => rfl)
    (Mid.mOut r M n hT)
    (Mid.phiP_cris n N) (fun _ => rfl) (fun _ => rfl) (Mid.phiP_cris n N) (fun _ => rfl) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.NuPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuRed

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_phiP {m n : ℕ} (h : n ≤ m) (N : ℕ) (x : (base l).Acr m) :
    (base l).red h (Mid.phiP l m N x) = Mid.phiP l n N ((base l).red h x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiP_succ, Mid.phiP_succ, ← ih]; exact (pdOk_frob _).red_acr h _

def redLm (r : CrystallineSemistableComparison.Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (Mid.Lm r M m) (Mid.Lm r M n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl

def redLc (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true m) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (B.red_κb _ true h)) fun _ _ _ => rfl

theorem ptOut_snd (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) (n : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F n hT).app B₀ y).1.2 = y.1.2 := rfl

theorem nu_pt (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) {m n : ℕ} (h : n ≤ m)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F m hT).app B₀ ((B.basePt F _ (red_κm r h)).app B₀ y)).1.2 =
      ((B.basePt F _ (B.red_κb _ true h)).app B₀ ((Mid.ptOut F n hT).app B₀ y)).1.2 := by
  rw [ptOut_snd, SH.base_snd, SH.base_snd, ptOut_snd]

theorem nu_red : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j),
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  intro l _ K r N hT M n j x
  unfold Mid.nu Mid.nuMor B.redHc B.redMor redT
  exact cr_square (Mid.mOut r M (n + 1) hT) (redLm r M (Nat.le_succ n)) (redLc M (Nat.le_succ n)) (Mid.mOut r M n hT)
    (Mid.phiP_cris _ N) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Mid.phiP_cris _ N)
    (red_phiP (Nat.le_succ n) N) (nu_pt r hT _ (Nat.le_succ n)) j x

end GlobalTheory.CompanionTheory.NuRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMap
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem idx_self_eq {d : ℕ} (I : Idx d d) : I.1 = id := by
  have hs : Function.Surjective I.1 := Finite.injective_iff_surjective.1 I.2.injective
  exact (StrictMono.range_inj I.2 strictMono_id).1 (by rw [hs.range_eq, Set.range_id])

theorem sum_idx_self {M : Type*} [AddCommMonoid M] {d : ℕ} [Fintype (Idx d d)] (g : Idx d d → M) :
    ∑ I, g I = g ⟨id, strictMono_id⟩ := by
  letI : Unique (Idx d d) :=
    { default := ⟨id, strictMono_id⟩, uniq := fun I => Subtype.ext (idx_self_eq I) }
  exact Fintype.sum_unique g

section Form
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d j : ℕ}
  (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (I : Fin j → Fin d) (u : ComposableArrows C j)

theorem form_add_fun (x x' : Φ.A.obj E.D) : E.form σ I (x + x') u = E.form σ I x u + E.form σ I x' u := by
  simp only [Frame.form, map_add (f := _), mul_add]

theorem form_sub_fun (x x' : Φ.A.obj E.D) : E.form σ I (x - x') u = E.form σ I x u - E.form σ I x' u := by
  simp only [Frame.form, map_sub, mul_sub]

theorem form_alg_mul (a : R) (x : Φ.A.obj E.D) :
    E.form σ I (algebraMap R _ a * x) u = a • E.form σ I x u := by
  simp only [Frame.form, map_mul, AlgHom.commutes, Algebra.smul_def]
  ring

end Form

theorem coef_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  intro K _ _ X q W d t s E ε hL σ r hr hs
  letI := (strV q W).toAlgebra
  obtain ⟨hE, hU⟩ := _root_.GlobalTheory.CompanionTheory.ConeLocal.loc_coef q t s E ε hL σ d r hr hs
  have ex : ∀ c : HQ (KS q s {W}) r (r + 1) d, ∃ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c := by
    intro c
    obtain ⟨y, hy⟩ := hE c
    refine ⟨y ⟨id, strictMono_id⟩, ?_⟩
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε (y I)) u) = E.form σ id (ε (y ⟨id, strictMono_id⟩)) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε (y I)) u)
    rwa [e] at hy
  have z0 : ∀ y : Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) 0 → y = 0 := by
    intro y h
    have e : (fun u => ∑ I : Idx d d, E.form σ I.1 (ε ((fun _ => y : Idx d d → Γ(X, W)) I)) u) = E.form σ id (ε y) :=
      funext fun u => sum_idx_self (fun I : Idx d d => E.form σ I.1 (ε y) u)
    exact congrFun (hU (fun _ => y) (by rwa [e])) ⟨id, strictMono_id⟩
  have uniq : ∀ (y y' : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c →
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y')) c → y = y' := by
    intro y y' c h h'
    have h2 := rep_add h (rep_smul (-1 : K) h')
    have e : (fun u => E.form σ id (ε y) u + (-1 : K) • E.form σ id (ε y') u) = E.form σ id (ε (y - y')) := by
      funext u
      rw [map_sub, form_sub_fun, neg_one_smul, sub_eq_add_neg]
    rw [e, neg_one_smul, add_neg_cancel] at h2
    exact sub_eq_zero.1 (z0 _ h2)
  choose φ hφ using ex
  refine ⟨{ toFun := φ, map_add' := ?_, map_smul' := ?_ }, ?_, fun y c h => uniq _ _ c (hφ c) h⟩
  · intro c c'
    refine uniq _ _ (c + c') (hφ _) ?_
    have h2 := rep_add (hφ c) (hφ c')
    have e : (fun u => E.form σ id (ε (φ c)) u + E.form σ id (ε (φ c')) u) = E.form σ id (ε (φ c + φ c')) := by
      funext u
      rw [map_add (f := _), form_add_fun]
    rwa [e] at h2
  · intro a c
    refine uniq _ _ (a • c) (hφ _) ?_
    have h2 := rep_smul a (hφ c)
    have e : (fun u => a • E.form σ id (ε (φ c)) u) = E.form σ id (ε (a • φ c)) := by
      funext u
      have e1 : a • φ c = strV q W a * φ c := Algebra.smul_def a (φ c)
      rw [e1, map_mul, hL.2.2.1 a, form_alg_mul]
    rwa [e] at h2
  · intro c c' h
    have h' : φ c = φ c' := h
    have h2 := hφ c'
    rw [← h'] at h2
    exact rep_unique (hφ c) h2

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

def twSecs {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules} (S : Subobject P) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤)

def twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  ((Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤))

structure OpSeq {X : Scheme.{0}} (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (d : ℕ) : Prop where
  coherent : ∀ e, IsCoherent (M e)
  comm : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)
  gen : ∀ e, d ≤ e → ∀ U : X.affineOpens,
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤

def GradedNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (k : ℕ) (M : ℕ → Type)
    [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)] [∀ e, Module.Finite R (M e)]
    (T : Fin k → ∀ e, M e →ₗ[R] M (e + 1)),
    (∀ i j e x, T j (e + 1) (T i e x) = T i (e + 1) (T j e x)) →
    ∀ d : ℕ, (∀ e, d ≤ e → ⨆ i, LinearMap.range (T i e) = ⊤) →
    ∀ L : ∀ e, Submodule R (M e), (∀ i e, (L e).map (T i e) ≤ L (e + 1)) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ⨆ i, (L e).map (T i e) = L (e + 1)

def UniformVanishing : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q)

def UniformGen : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, d ≤ e →
      Submodule.span Γ(X, ⊤)
        (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (T i e)).app ⊤)) = ⊤

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittAcrisFlat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatW

theorem eq_zero_of_pow_mul_eq_zero {l : ℕ} [Fact l.Prime] (m : ℕ) {x : Acris l}
    (h : (l : Acris l) ^ m * x = 0) : x = 0 := by
  induction m with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply ACris.eq_zero_of_p_mul_eq_zero (K := ℂ_[l]) (p := l)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem flat_AW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) :
    Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro a ha
  obtain ⟨⟨y, hy0⟩, hy⟩ := (Submodule.mem_torsion_iff _).1 ha
  have hne : y ≠ 0 := nonZeroDivisors.ne_zero hy0
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y hne
  have hu : IsUnit (r.w (b : WittVector l r.k)) := b.isUnit.map r.w
  have key : ∀ x : Acris l, r.w y * x = 0 → x = 0 := by
    intro x h
    rw [e, map_mul, map_pow, map_natCast] at h
    apply eq_zero_of_pow_mul_eq_zero m
    apply hu.mul_right_eq_zero.1
    linear_combination h
  exact (Submodule.mem_bot _).2 (key a hy)

end GlobalTheory.CompanionTheory.FlatW
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompat
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BaseChangeFrob

theorem cr_square_gen {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [CommRing Λ₁] [CommRing Λ₂] [CommRing Λ₃] [CommRing Λ₄]
    {c₁ : Λ₁ →+* b₁.R} {c₂ : Λ₂ →+* b₂.R} {c₃ : Λ₃ →+* b₃.R} {c₄ : Λ₄ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R}
    {τa : Λ₁ →+* Λ₂} {τb : Λ₂ →+* Λ₄} {τc : Λ₁ →+* Λ₃} {τd : Λ₃ →+* Λ₄}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : ∀ a, τb (τa a) = τd (τc a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI i₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI i₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨(RingHom.ext hτ).symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem w_frobenius (r : CrystallineSemistableComparison.Res l K) (w : WittVector l r.k) :
    ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w) := by
  change ACris.phi (K := ℂ_[l]) (p := l) (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) =
    algebraMap (Ainf l) (Acris l) (WittVector.map r.s (WittVector.frobenius w))
  rw [ACris.phi_algebraMap]
  congr 1
  change WittVector.frobenius (WittVector.map r.s w) = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [WittVector.map_coeff, frobenius_def, map_pow]

theorem wn_frob (r : CrystallineSemistableComparison.Res l K) (n : ℕ) (x : Wc.Wm l r.k n) :
    (base l).phi n (Mid.wn r n x) = Mid.wn r n (Wc.frob l r.k n x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Wc.frob_mk', Mid.wn_mk, Mid.wn_mk, (base l).phi_cris, w_frobenius]

theorem phiM_bW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ)
    (y : (HSW r M j).M n) : phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  refine cr_square_gen (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Wc.phiM l (B.schFn M.p) r.ρ n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r n) ((base l).phi_cris n) (Wc.frob_mk' l r.k n) (Mid.wn_mk r n) (w_frobenius r) (wn_frob r n) ?_ j y
  intro B₀ y
  rfl

end GlobalTheory.CompanionTheory.BaseChangeFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonGaloisFixed
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BWGal

theorem gal_wn {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) (x : (Wc.bs l r.k n).R) :
    galBase σ n (Mid.wn r n x) = Mid.wn r n x := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Mid.wn_mk, galBase_cris, hσ]

abbrev bWM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Wc.L l (B.schFn M.p) r.ρ n) (Mid.Lm r M n) (Mid.wn r n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl

abbrev gM {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K)
    (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n : ℕ) :
    Mor (Mid.Lm r M n) (Mid.Lm r M n) (galBase σ n) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl

theorem bW_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (y : (HSW r M j).M n), galM r M σ hσ n j (bW r M n j y) = bW r M n j y := by
  intro l _ K r M σ hσ n j y
  haveI : RingHomCompTriple r.w (ACris.galCris σ) r.w := ⟨RingHom.ext hσ⟩
  refine (pull_pull r.w (bWMor r M n) (galT' r M σ hσ n) j y).trans ?_
  exact cr_pull_eq _ _ (fun T => crHom (T := (bWM r M n).obj ((gM r M σ hσ n).obj T)) (T' := (bWM r M n).obj T)
    (RingHom.id T.B) (fun x => congrArg T.i (gal_wn r σ hσ n x)) (DPMorphism.id T.δ).isDPMorphism
    fun h => (pt_id _ h _).trans rfl) (fun _ _ => rfl) (fun _ _ => rfl) j y

end GlobalTheory.CompanionTheory.BWGal
end
end

