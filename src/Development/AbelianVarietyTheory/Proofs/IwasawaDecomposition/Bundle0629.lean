module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceSide
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : GlobalTheory.Published.LocalLanglandsGL}

def Mv.sideA {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) : SideA m.D (m.cf cf) jE := @_root_.GlobalTheory.HeightCounting.SideA.mk (_) (_) (_)
    (bare := (A.bare))
    (wdT := (A.wdT))
    (lab := (A.lab))
    (chr := @_root_.GlobalTheory.HeightCounting.CharSide.mk (_) (_)
      (e1 := (A.chr.e1))
      (unr_iff := (A.chr.unr_iff))
      (frob := (A.chr.frob))
      (tw := (A.chr.tw))
      (infG := (A.chr.infG))
      (csd := (A.chr.csd))
      (etaT := (A.chr.etaT))
      (etaTinv := (A.chr.etaTinv))
      (plGw := (A.chr.plGw)))
    (row := @_root_.GlobalTheory.HeightCounting.RowSide.mk (_)
      (locR := (A.row.locR))
      (satR := (A.row.satR))
      (lab_eq := (A.row.lab_eq)))
    (pl := @_root_.GlobalTheory.HeightCounting.PlSide.mk (_)
      (ι := (A.pl.ι))
      (ι_w := (A.pl.ι_w))
      (plB := (A.pl.plB))
      (plB_eq := (A.pl.plB_eq))
      (plκ := (A.pl.plκ)))
    (iota := (A.iota))
    (wd := @_root_.GlobalTheory.HeightCounting.WDSide.mk (_) (_)
      (wdOf := (A.wd.wdOf))
      (wdOf_dim := (A.wd.wdOf_dim))
      (wdOf_unr := (A.wd.wdOf_unr))
      (wdOf_frob := (A.wd.wdOf_frob))
      (wdOf_ine := (A.wd.wdOf_ine))
      (wdOf_mono0 := (A.wd.wdOf_mono0))
      (IsCrysW := (A.wd.IsCrysW))
      (IsPotCrysW := (A.wd.IsPotCrysW))
      (IsdRW := (A.wd.IsdRW))
      (jumpsW := (A.wd.jumpsW))
      (wdOf_unrL := (A.wd.wdOf_unrL))
      (wdOf_mono0L := (A.wd.wdOf_mono0L))
      (away := (A.wd.away))
      (above := (A.wd.above))
      (loc := (A.wd.loc)))
    (grp := @_root_.GlobalTheory.HeightCounting.GrpSide.mk (_)
      (tA := (A.grp.tA))
      (tκ := (A.grp.tκ))
      (teichC_def := (A.grp.teichC_def))
      (ζ := (A.grp.ζ))
      (ζ_gen := (A.grp.ζ_gen))
      (O := (A.grp.O))
      (eSer_def := (A.grp.eSer_def))
      (kv := (A.grp.kv))
      (tg_tame := (A.grp.tg_tame))
      (O_equiv := (A.grp.O_equiv))
      (O_tw := (A.grp.O_tw)))
    (par := @_root_.GlobalTheory.HeightCounting.ParSide.mk (_) (_)
      (eM := (A.par.eM))
      (eM_K := (A.par.eM_K))
      (eP := (A.par.eP))
      (locPar_def := (A.par.locPar_def)))
    (au := @_root_.GlobalTheory.HeightCounting.AUSide.mk (_)
      (cls := (A.au.cls))
      (surj := (A.au.surj))
      (iso := (A.au.iso))
      (mult := (A.au.mult))
      (sph := (A.au.sph))
      (sat := (A.au.sat))
      (clsWt := (A.au.clsWt))
      (surjWt := (A.au.surjWt))
      (isoWt := (A.au.isoWt))
      (wt := (A.au.wt))
      (infW := (A.au.infW))
      (locUnr := (A.au.locUnr))
      (locPol := (A.au.locPol)))
    (chiT := (A.chiT))

def Mv.cg {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} (x : CGTrue hL D A.wdT) : CGTrue hL m.D (m.sideA A).wdT := @_root_.GlobalTheory.HeightCounting.CGTrue.mk (_) (_) (_)
    (e := (x.e))
    (surj := (x.surj))
    (zero := (x.zero))
    (loc := (x.loc))
    (tw := (x.tw))
    (inf := (x.inf))
    (csd := (x.csd))
theorem Mv.au {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} (x : AUTrue hL D A.wdT A.au) : AUTrue hL m.D (m.sideA A).wdT (m.sideA A).au := (x)
theorem Mv.row {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {rep} (x : RowTrue hL D rep (fun σ w ↦ (A.wdT.e w) (A.row.locR σ w)) A.row.satR) : RowTrue hL m.D rep (fun σ w ↦ ((m.sideA A).wdT.e w) ((m.sideA A).row.locR σ w)) (m.sideA A).row.satR := (x)

section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.mtInput (x : MtInput D M tp.tup C.Q) : MtInput m.D (m.mt M) (m.tp tp).tup (m.ch C).Q := @_root_.GlobalTheory.HeightCounting.MtInput.mk (_) (_) (_) (_)
    (prod := (x.prod))
    (para := (x.para))
    (uni := (x.uni))
    (hyp := (x.hyp))
    (wt := (x.wt))
    (rat := (x.rat))
    (int := (x.int))
    (full := (x.full))

def Mv.ratIn {S} (x : RatIn D S) : RatIn m.D S := @_root_.GlobalTheory.HeightCounting.RatIn.mk (_) (_)
    (Sb := (x.Sb))
    (rho := (x.rho))
    (chi := (x.chi))
    (ks := (x.ks))
    (fd := (x.fd))
    (mk_fg := (x.mk_fg))
    (hL := (x.hL))
    (hs := (x.hs))
    (hL_zero := (x.hL_zero))
    (θ := (x.θ))
    (θ_ne := (x.θ_ne))
    (eig := (x.eig))
    (span := (x.span))
    (hL_int := (x.hL_int))
theorem Mv.rowDepth {rep} (x : RowDepth D rep) : RowDepth m.D rep := (x)
end

def Mv.host (x : HostTied D) : HostTied m.D := @_root_.Formalism.L2.Host.HostTied.mk (_)
    (fr := (x.fr))
    (jLL := (x.jLL))
    (embLL := (x.embLL))
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}

def Mv.chrN (x : NCharTied D cf C tp) : NCharTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NCharTied.mk (_) (_) (_) (_)
    (e1 := (x.e1))
    (unr_iff := (x.unr_iff))
    (frob := (x.frob))
    (tw := (x.tw))
    (infG := (x.infG))
    (csd := (x.csd))
    (muC := (x.muC))
    (etaT := (x.etaT))
    (etaTinv := (x.etaTinv))
    (plGw := (x.plGw))
theorem Mv.chrGal (x : NGalChrTied D cf C tp) : NGalChrTied m.D (m.cf cf) (m.ch C) (m.tp tp) := @_root_.Formalism.L2.Host.NGalChrTied.mk (_) (_) (_) (_)
    (psi_is := (x.psi_is))
    (psiL := (x.psiL))
    (deltaRead := (x.deltaRead))
theorem Mv.oSplit (x : GlobalTheory.SplitCoef.OSplit D) : GlobalTheory.SplitCoef.OSplit m.D := (x)
theorem Mv.large (x : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large m.D := (x)
theorem Mv.bkLaw (x : BkLaw D) : BkLaw m.D := (x)

def Mv.omFrame (x : Formalism.L2.OmFrame D) : Formalism.L2.OmFrame m.D := @_root_.Formalism.L2.OmFrame.mk (_)
    (jE := (x.jE))
    (eOm := (x.eOm))
    (comm := (x.comm))
end

theorem Mv.pack_pre {D₀ : D7} {L : LocAll (lay0 D₀)} (m : Mv (withLoc L)) {cf : CharFrame D₀} {C : NChoice D₀} (tp : TupTied D₀ cf C) :
    (⟨m.D, m.cf (cfL L cf), m.ch (chL L C), m.tp (tpL L tp)⟩ : Σ D : D7, Σ c : CharFrame D, Σ C : NChoice D, TupTied D c C) =
      ⟨withLoc (m.pre.loc L), cfL (m.pre.loc L) (m.pre.cf cf), chL (m.pre.loc L) (m.pre.ch C), tpL (m.pre.loc L) (m.pre.tp tp)⟩ :=
  (@Eq.refl (@Sigma D7 fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@Sigma.mk D7 (fun D ↦ @Sigma (CharFrame D) fun c ↦ @Sigma (NChoice D) fun C ↦ TupTied D c C) (@D (@withLoc D₀ L) m) (@Sigma.mk (CharFrame (@D (@withLoc D₀ L) m)) (fun c ↦ @Sigma (NChoice (@D (@withLoc D₀ L) m)) fun C ↦ TupTied (@D (@withLoc D₀ L) m) c C) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) (@Sigma.mk (NChoice (@D (@withLoc D₀ L) m)) (fun C ↦ TupTied (@D (@withLoc D₀ L) m) (@Mv.cf (@withLoc D₀ L) m (@cfL D₀ L cf)) C) (@ch (@withLoc D₀ L) m (@chL D₀ L C)) (@Mv.tp (@withLoc D₀ L) m (@cfL D₀ L cf) (@chL D₀ L C) (@tpL D₀ L cf C tp))))))

end GlobalTheory.LayerMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstForm
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.ConstForm

theorem constForm : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ (∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) → Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := Core.logDom_facts n a
  have hDp : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    Core.isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => Core.logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatFam.exists_analytic_locBasis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => Core.mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩
  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply Core.eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]
  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex
  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ s ∈ logDom n a, ∀ c : Fin r₀ → ℤ,
      ∑ j, c j • ζ (logExp a s) j = ∑ k, (∑ i, c i • A i) k • lam s k := by
    intro s hs c
    simp only [fun i => hA i s hs, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ (s : Fin n → ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∀ x y : Fin (2 * g) → ℤ,
      (hermForm Hm (∑ k, x k • lam s k) (∑ k, y k • lam s k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro s Hm hHm x y
    rw [Core.hermForm_im_sum]
    simp only [hHm, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq s₀ hs₀, hform s₀ Hm₀ hM₀, Complex.ofReal_intCast] at h4
    exact Core.dvd_of_exp_eq_one _ N hN h4
  refine ⟨2 * g, lam, M, hlamD.continuousOn, fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ,
    Core.span_top_of_isLatBasis (hlamB s hs) (hin s hs).choose_spec.2.2.1, (hlamB s hs).2⟩, fun s hs => ?_, hM,
    fun N hN => ?_⟩
  · obtain ⟨Hm, -, hpos, -, hint, hpair⟩ := hin s hs
    exact ⟨Hm, hpos, hM s hs Hm hint hpair⟩
  · obtain ⟨S, hcard, hSd⟩ := hdvd N hN
    refine ⟨S, hcard, fun u u' hu s hs Hm hHm => ?_⟩
    obtain ⟨m, hm⟩ := hSd u u' hu
    refine ⟨m, ?_⟩
    rw [hsum_eq s hs u, hsum_eq s hs u', hform s Hm hHm, hm]
    push_cast
    ring

end GlobalTheory.ShFam.Hor.LogCh.ConstForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegFlFlagMapRenamePerm
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.Schubert

theorem degFl_rename_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (ρ : ι → Equiv.Perm (Fin N))
    (P : MvPolynomial (ι × Fin N) ℝ) :
    Formalism.DegreeFormula.degFl ι N (rename (fun x : ι × Fin N => (x.1, ρ x.1 x.2)) P) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * Formalism.DegreeFormula.degFl ι N P := by
  set f : ι × Fin N → ι × Fin N := fun x => (x.1, ρ x.1 x.2) with hfdef
  have hinj : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [(ρ a).injective h2]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, j⟩
    exact ⟨(a, (ρ a).symm j), by simp [hfdef]⟩
  have hexp : ∀ σ : ι → Equiv.Perm (Fin N),
      Formalism.DegreeFormula.permExp (σ * ρ⁻¹) = (Formalism.DegreeFormula.permExp σ).mapDomain f := by
    intro σ
    ext y
    obtain ⟨⟨a, i⟩, rfl⟩ := hsurj y
    rw [Finsupp.mapDomain_apply_of_injective hinj]
    simp [Formalism.DegreeFormula.permExp, hfdef, Pi.mul_apply, Pi.inv_apply]
  have hsgn : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign ((σ * ρ⁻¹) τ) : ℤ) : ℝ)) =
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Pi.mul_apply, Pi.inv_apply, Equiv.Perm.sign_inv]
  have key : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        (rename f P).coeff (Formalism.DegreeFormula.permExp σ) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * ∑ σ : ι → Equiv.Perm (Fin N),
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (Formalism.DegreeFormula.permExp σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (ρ⁻¹ : ι → Equiv.Perm (Fin N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.coe_mulRight, hsgn, hexp, coeff_rename_mapDomain _ hinj]
    ring
  unfold Formalism.DegreeFormula.degFl
  rw [key]
  ring

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perm_val_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) (i : ℕ) (h1 : i < Dw.mult a) (h2 : i < Dw.mult b) :
    ((w a ⟨i, h1⟩ : Fin (Dw.mult a)) : ℕ) = ((w b ⟨i, h2⟩ : Fin (Dw.mult b)) : ℕ) := by
  subst e; rfl

theorem sign_perm_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) : Equiv.Perm.sign (w a) = Equiv.Perm.sign (w b) := by
  subst e; rfl

def flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm (Fin (Dw.p + Dw.q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr
    ((finCongr (GlobalTheory.PointChern.mult_of_mem Dw τ.2)).permCongr (w τ.1))
    (Fin.revPerm.permCongr ((finCongr (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ))).permCongr
      (w (conjEmb τ.1)))))

theorem sign_flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm.sign (flagPerm Dw w τ) = Equiv.Perm.sign (w τ.1) * Equiv.Perm.sign (w (conjEmb τ.1)) := by
  simp only [flagPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem flagPerm_big {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    ((flagPerm Dw w τ ⟨i, hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) = ((w τ.1 i : Fin (Dw.mult τ.1)) : ℕ) := by
  have hp : (i : ℕ) < Dw.p := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw τ.2; omega
  have e : (⟨i, hi⟩ : Fin (Dw.p + Dw.q)) = Fin.castAdd Dw.q ⟨i, hp⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd, Equiv.permCongr_apply]
  simp

theorem flagPerm_small {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) {σ : E →+* ℂ}
    (hσ : ¬ σ (H.rt : E) = H.rt0) (i : Fin (Dw.mult σ)) (hi : Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p + Dw.q) :
    ((flagPerm Dw w ⟨conjEmb σ, GlobalTheory.AllWt.conj_mem hσ⟩ ⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) =
      Dw.p + (Dw.q - 1 - ((w σ i : Fin (Dw.mult σ)) : ℕ)) := by
  have hq : (i : ℕ) < Dw.q := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw hσ; omega
  have e : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p ⟨Dw.q - 1 - i, by omega⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, finCongr_apply, finCongr_symm, Fin.coe_cast]
  have key : ∀ x : Fin (Dw.mult (conjEmb (conjEmb σ))), (x : ℕ) = (i : ℕ) →
      ((w (conjEmb (conjEmb σ)) x : Fin _) : ℕ) = ((w σ i : Fin (Dw.mult σ)) : ℕ) := by
    rintro ⟨x, hx⟩ hxi
    simp only at hxi
    subst hxi
    exact perm_val_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb σ) _ _ i.2
  rw [key _ (by simp; omega)]
  omega

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagMap_rename {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    flagMap Dw (rename (fun x : GlobalTheory.GoodMetric.Root Dw.mult =>
        (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q) =
      rename (fun x : GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) => (x.1, flagPerm Dw w x.1 x.2)) (flagMap Dw Q) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun x => ?_
  simp only [AlgHom.comp_apply, rename_X, flagMap, aeval_X]
  obtain ⟨σ, i⟩ := x
  by_cases h : σ (H.rt : E) = H.rt0
  · simp only [flagRoot, dif_pos h, rename_X]
    congr 2
    exact Fin.ext (flagPerm_big Dw w ⟨σ, h⟩ i _).symm
  · simp only [flagRoot, dif_neg h, map_neg, rename_X]
    congr 3
    exact Fin.ext (flagPerm_small Dw w h i _).symm

theorem prod_sign_eq {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) :
    (∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) = ∏ τ : GlobalTheory.AllWt.Psi H, Equiv.Perm.sign (flagPerm Dw w τ) := by
  simp only [sign_flagPerm, Finset.prod_mul_distrib]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  refine Fintype.prod_equiv
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) } _ _ ?_
  intro τ
  simp only [Equiv.coe_fn_mk]
  exact sign_perm_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb τ.1).symm

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

theorem degFl_flagMap_rename_perm (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw (MvPolynomial.rename
              (fun x : GlobalTheory.GoodMetric.Root Dw.mult => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q)) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) *
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
  rw [flagMap_rename, degFl_rename_perm, prod_sign_eq]
  push_cast
  rfl

end GlobalTheory.Schubert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChangeStatement
section
namespace GlobalTheory.T

alias divisionLocalData_preserved_divisionLatticeChange := GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv

end GlobalTheory.T
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjectiveStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intBilinForm_descend_along_surjective : ∀ {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y), Function.Surjective f → ∀ β : LinearMap.BilinForm ℤ X,
  (∀ x, f x = 0 → ∀ y, β x y = 0) → (∀ x, f x = 0 → ∀ y, β y x = 0) →
  ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  first | exact @GlobalTheory.exists_bilinForm_descend_of_surjective | exact GlobalTheory.exists_bilinForm_descend_of_surjective | (intros; apply GlobalTheory.exists_bilinForm_descend_of_surjective <;> assumption)
end

