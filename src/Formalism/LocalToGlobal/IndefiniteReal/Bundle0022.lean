module

public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelFrame
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BesselDerivatives.ExpSup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CongNormal
section
noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SS

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]


def fixN (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (N : ℕ) : Submodule ℂ A where
  carrier := {a | ∀ κ, Formalism.L2.NG.Cong L n N κ → ρ κ a = a}
  zero_mem' := fun κ _ => map_zero _
  add_mem' := fun ha hb κ hκ => by rw [map_add (f := _), ha κ hκ, hb κ hκ]
  smul_mem' := fun c a ha κ hκ => by rw [map_smul, ha κ hκ]

def IsEqvA (ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A) (π : Formalism.L2.NG.FinTyp L n) (Φ : π.S →ₗ[ℂ] A) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), Φ ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ = ρ h (Φ f)

end SS

end Formalism.IndefR.principalLevelFrame
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CutPassage3SOfSteps
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

theorem rep_apply (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (g : G) (x : Fin I.Sg.D → K) :
    I.rep h1 hm g x = I.ρf g *ᵥ x := by
  first
  | rfl
  | simp [rep, Matrix.toLin'_apply]

theorem epM_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    (I.epM P ψ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP P χ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [epM, Formalism.IndefR.TransferLatticeStatement.epP, map_smul, map_sum, hχ, map_inv]
  congr 1
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun h _ => ?_)
  have e := hχ h⁻¹
  rw [map_inv χ, map_inv ψ] at e
  rw [e]
  rfl

theorem eMat_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) {W : Type} [AddCommGroup W]
    [Module K W] (τ : Representation K G W) :
    (I.eMat τ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS τ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eMat, Formalism.IndefR.TransferLatticeStatement.eS, map_smul, map_sum]
  rfl

theorem passage_of_steps [_root_.NumberField.IsTotallyComplex K] {s : ℕ} (H : I.Hyp s) {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) (N : IndefNum I.A3.fam3.base3)
    (hρ : I.PRho) (hJ : I.PJ) (hR : I.PRange) (hMet : I.PMet) (hFr : I.PFrames) (hU : I.PUni)
    (hLat : I.PLat) (hGL : I.PGLat) (hS : I.PSand) (hGood : I.PGood τ)
    (hτ : Formalism.IndefR.TransferLatticeStatement.IsGood τ) (hX : CharsX τ I.A.fam.X) (hM1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨I.P0, I.ψ0⟩) (hn : 0 < nbar)
    (hM2 : NearConstantMultiplicities τ ⟨I.P1, I.ψ1⟩ nbar N.de) (hla : N.la = Formalism.IndefR.IndefiniteEpsilonOperator.la G) :
    Passage N (I.Sb false) (I.Sb true) := by
  obtain ⟨h1, hm, -⟩ := hρ s H
  obtain ⟨χ0, hχ0⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0
  obtain ⟨χ1, hχ1⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1
  have hFrm : (I.LA τ nbar).FramesG := hFr s H
  have hL : (I.LA τ nbar).LatG := by
    classical
    letI : Finite T := H.ok.ok2.tup_fin
    letI : Fintype T := Fintype.ofFinite T
    let L : T → Submodule (𝓞 K) (Fin I.Sg.D → K) := fun t => matLat (I.X.rowMat I.cg false t)
      ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t)
    have hfull : ∀ t, Submodule.IsFullLattice K (L t) := fun t =>
      matLat_full _ (rowG_surj H t) _
        (BlockDat.Lam_full H.ok.ok2.conj (H.ok.ok2.what₂ t) H.ok.ok2.irr)
    choose a ha0 ha using fun t => GluingInclusion.denom (K := K) (L I.A3.fam3.base3.μ0) (L t)
      (Submodule.IsLattice.fg (self := (hfull _).toIsLattice)) (hfull t).span_eq_top
    let d := ∏ t, a t
    have hd : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => ha0 t)
    have hle : ∀ x ∈ L I.A3.fam3.base3.μ0, x ∈ Submodule.span K (I.Sg.RR : Set _) := by
      intro x hx
      have hdx : d • x ∈ I.Sg.RR := by
        apply (I.mem_RRg).2
        intro w
        obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ (I.X.μ w))
        have hdmem : d • x ∈ L (I.X.μ w) := by
          change (∏ t, a t) • x ∈ L (I.X.μ w)
          rw [hr, mul_comm, mul_smul]
          exact (L _).smul_mem r (ha _ x hx)
        obtain ⟨z, hz, hz'⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hdmem
        refine ⟨1, one_mem _, z, hz, ?_⟩
        rw [one_smul]
        exact hz'
      have hdK : algebraMap (𝓞 K) K d ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne hd
      have hmem : d • x ∈ Submodule.span K (I.Sg.RR : Set (Fin I.Sg.D → K)) :=
        Submodule.subset_span hdx
      have hs := (Submodule.span K (I.Sg.RR : Set (Fin I.Sg.D → K))).smul_mem
        (algebraMap (𝓞 K) K d)⁻¹ hmem
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hdK, one_smul] at hs
      exact hs
    refine { toIsLattice := hLat s H, span_eq_top := ?_ }
    exact top_unique (by rw [← (hfull I.A3.fam3.base3.μ0).span_eq_top]; exact Submodule.span_le.mpr hle)
  have key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0
  have key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1
  have hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm) := fun t =>
    I.eMat_eq h1 hm (τ t)
  have hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1 := fun t =>
    nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1
  have hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0 := fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t
  have hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id := by
    unfold Formalism.IndefR.TransferLatticeStatement.eGood
    rw [← Finset.sum_congr rfl fun t _ => hs t]
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)
    simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx
    rw [LinearMap.sum_apply, LinearMap.id_apply]
    simpa only [Matrix.mulVecLin_apply] using hx
  have hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR := fun g a ha => by
    rw [rep_apply]; exact hGL s H g a ha
  have hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm) := fun v g x y => by
    rw [rep_apply, rep_apply]; exact hU s H v g x y
  obtain ⟨hRk, hD0, hD1, hMx⟩ := Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1'
    key0 key1 hs hnS rfl hgood hFrm hL hst hUn
  have hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE := fun b =>
    ⟨(hJ s H b).2, hR s H b, hMet s H b⟩
  have hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR := by
    intro b
    obtain ⟨hin, hout⟩ := hS s H b
    refine ⟨?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hin x hx, ?_⟩
      show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin
      rw [← hR s H b]; exact ⟨x, rfl⟩
    · rintro y ⟨hyR, hyE⟩
      obtain ⟨x, hx, hxy⟩ := hout y hyR hyE
      exact ⟨x, hx, hxy⟩
  have hRows : (I.LA τ nbar).RowsG :=
    ⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false),
      Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩
  have hSz : (I.LA τ nbar).Sizes N.la := by
    refine ⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩
    · exact (Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le
    · exact (Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le
    · rw [hla]; exact le_refl _
  exact passage_from_levels K I.A3.fam3.base3 _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true)
    (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows

end In3

def Steps3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ)
    (I : In3 K G Pl0 I0 Ty T m), I.PRho ∧ I.PJ ∧ I.PRange ∧ I.PMet ∧ I.PFrames ∧ I.PUni ∧ I.PLat ∧ I.PGLat ∧ I.PSand ∧
      ∀ (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
        [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)), I.PGood τ

theorem cutPassage3S_of_steps (h : Steps3) : CutPassage3S := by
  intro K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar
    hok hsep hst hin h4 hp0 hp1 hh2 hrat hh2g hratg hgu hge hn0 hn1 hτ hX hM1 hn hM2 hla
  let I : In3 K G Pl0 I0 Ty T m := ⟨A3, P0, ψ0, P1, ψ1, Dc, Sp, Zsc, X, gE⟩
  obtain ⟨hρ, hJ, hR, hMet, hFr, hU, hLat, hGL, hS, hG⟩ := h K G Pl0 I0 Ty T m I
  exact I.passage_of_steps ⟨hok, hsep, hst, hin, h4, hp0, hp1, hh2, hrat, hh2g, hratg, hgu, hge, hn0, hn1⟩
    τ nbar _ hρ hJ hR hMet hFr hU hLat hGL hS (hG S Ws τ) hτ hX hM1 hn hM2 hla

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open Formalism.L2.Theta

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem countable_GQ (V : HSp D) : Countable (GQ V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem borel_GA (V : HSp D) : BorelSpace (GA D V) :=
  Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA (F := D.host.F) (E := D.host.E) D.sp.cm.sig V.gram

theorem petPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) : PetPos V μ 𝓕 := by
  intro F hc hinv hne hint
  have := countable_GQ V
  have := measurableMul_GA V
  have := borel_GA V
  have := hH
  set U : Set (GA D V) := {g | F g ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun hc continuous_const
  have hUne : U.Nonempty := by
    by_contra h
    apply hne
    funext g
    by_contra hg
    exact h ⟨g, hg⟩
  have hUpos : 0 < μ U := hUo.measure_pos μ hUne
  have hnn : 0 ≤ᵐ[μ.restrict 𝓕] fun g => ‖F g‖ ^ 2 := ae_of_all _ (fun g => by positivity)
  refine lt_of_le_of_ne (integral_nonneg fun g => by positivity) ?_
  intro h0
  have hz : (fun g => ‖F g‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0.symm
  have hset : {g : GA D V | ¬ (‖F g‖ ^ 2 = (0 : GA D V → ℝ) g)} = U := by
    ext g
    simp [hUdef]
  have hFU : μ (U ∩ 𝓕) = 0 := by
    have h1 := ae_iff.1 hz
    rw [hset, Measure.restrict_apply hUo.measurableSet] at h1
    exact h1
  have key : U ≤ᵐ[μ] (⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) : Set (GA D V)) := by
    filter_upwards [hF.ae_covers] with x hx hxU
    obtain ⟨γ, hγ⟩ := hx
    refine Set.mem_iUnion.2 ⟨γ, ?_, ?_⟩
    · show F ((γ : GA D V) * x) ≠ 0
      rw [hinv _ γ.2 x]
      exact hxU
    · exact hγ
  have hU0 : μ U = 0 := by
    refine le_antisymm ((measure_mono_ae key).trans ?_) bot_le
    refine (measure_iUnion_le _).trans ?_
    simp only [measure_preimage_mul, hFU, tsum_zero, le_refl]
  exact hUpos.ne' hU0

end Formalism.IndefR.PeterssonHilbertSpace

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SmExpSmulContDiff
section
noncomputable section

open Matrix Topology Filter
open scoped ContDiff InnerProductSpace

namespace Formalism.IndefR.PeterssonHilbertSpace

section Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma sm_exp_smul_contDiff (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun s : ℝ => NormedSpace.exp (s • X)) := by
  have h := PI.BesselDerivW.exp_contDiff X
  simpa only [Complex.coe_smul] using h

lemma sm_prod_exp_contDiff : ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    ContDiff ℝ ∞ (fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod)
  | 0, Xs => by simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin 0 → ℝ => (1 : Matrix (Fin n) (Fin n) ℂ))
  | k + 1, Xs => by
    have ih := sm_prod_exp_contDiff k (fun i => Xs i.succ)
    have h1 : ContDiff ℝ ∞ (fun t : Fin (k + 1) → ℝ => NormedSpace.exp (t 0 • Xs 0)) :=
      (sm_exp_smul_contDiff (Xs 0)).comp (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin (k + 1)))
    have h2 : ContDiff ℝ ∞ (fun t : Fin (k + 1) → ℝ =>
        (List.ofFn fun i : Fin k => NormedSpace.exp (t i.succ • Xs i.succ)).prod) :=
      ih.comp (contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ)
    simp only [List.ofFn_succ, List.prod_cons]
    exact PI.KFinSmoothW.Gard.contDiff_mat_mul h1 h2

lemma sm_prod_exp_mem (G : Matrix (Fin n) (Fin n) ℂ) : ∀ (k : ℕ) (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    (∀ i, (Xs i)ᴴ * G + G * Xs i = 0) → ∀ t : Fin k → ℝ,
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod)ᴴ * G *
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod = G
  | 0, Xs, _, t => by simp
  | k + 1, Xs, hX, t => by
    have ih := sm_prod_exp_mem G k (fun i => Xs i.succ) (fun i => hX i.succ) (fun i => t i.succ)
    have hl : (t 0 • Xs 0)ᴴ * G + G * (t 0 • Xs 0) = 0 := by
      have h := CCRuleCW.lie_smul G (Xs 0) (hX 0) (t 0)
      simpa only [Complex.coe_smul] using h
    have he := CCRuleCW.exp_mem_UH G (t 0 • Xs 0) hl
    have hm := CCRuleCW.UH_mul G _ _ he ih
    simp only [List.ofFn_succ, List.prod_cons]
    exact hm

lemma sm_transfer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (Lie : Set (Matrix (Fin n) (Fin n) ℂ))
    (hLie : ∀ X ∈ Lie, Xᴴ * G + G * X = 0) (w : H)
    (hs : PI.UpqRep.SmoothOnH (PI.UpqRep.Jm ε) (fun g => σ g w)) :
    Formalism.L2.Theta.SmoothVec Lie (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hX
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP)
  have hc : ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) :=
    PI.KFinSmoothW.Gard.contDiff_mat_mul
      (PI.KFinSmoothW.Gard.contDiff_mat_mul contDiff_const (sm_prod_exp_contDiff k Xs)) contDiff_const
  have hmem : ∀ t : Fin k → ℝ, PI.UpqRep.inUH (PI.UpqRep.Jm ε)
      (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) := by
    intro t
    have hQ := sm_prod_exp_mem G k Xs (fun i => hLie _ (hX i)) t
    set Q := (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod
    show (P * Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q * P⁻¹)
        = (P⁻¹)ᴴ * (Qᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hG, hQ]
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hinv]; simp
  rw [contDiff_iff_contDiffAt]
  intro t0
  obtain ⟨U, F, hU, h0, hF, hEq⟩ := hs _ (hmem t0)
  have hev : (fun t : Fin k → ℝ => σ (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) w)
      =ᶠ[𝓝 t0] fun t => F (P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) := by
    filter_upwards [hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hEq _ ht (hmem t)
  exact ((hF.contDiffAt (hU.mem_nhds h0)).comp t0 hc.contDiffAt).congr_of_eventuallyEq hev

lemma sm_isURepOn_bridge (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    PI.UpqRep.IsURepOn (PI.UpqRep.UJset ε) σ :=
  ⟨⟨h.1.1, fun a ha b hb => h.1.2 a ha b hb⟩, fun g hg v => h.2.1 g hg v, fun v => h.2.2 v⟩

end Gen

section MultSec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S
open Formalism.L2.Theta Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

end MultSec

end Formalism.IndefR.PeterssonHilbertSpace

end
end

