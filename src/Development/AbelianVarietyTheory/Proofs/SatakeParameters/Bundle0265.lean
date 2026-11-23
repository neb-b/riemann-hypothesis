module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumInvarianceSupportTransportFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsReadingStepMoveBasePointsOneOffLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumInvarianceSupportKernelChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV.EntrySupportBounds

open GlobalTheory.Mem.Col2 GlobalTheory.TopStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} {u : Pr.Word}

theorem top_supp (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) (x : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hx : XiTop Ch sel mu cst (m2 + 1) p Y p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm] at hx
  unfold xiOver at hx
  refine GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q s l => ?_
  have h := GlobalTheory.GO.locTop_den hL.hm hL.cst_ok (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _)) s
    (Fin.cast (congrArg R.N hm) l)
  simpa [castSp, LinearMap.funLeft_apply] using h

open Classical in
theorem top_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (p' : ChPt (R := R) sel mu u (m2 + 1 + 1))
    (hY : ∀ (Q : rowSG Pr sel mu) l, IntAt Q.1 ((qOf Q.1 : X.E) ^ (if Q.1 ∈ Pr.vGs then 1 else cst.M) * (frsF sel mu p Q).symm (repY Y) l))
    (x y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst (m2 + 1) p Y p' (x + y) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  have hm : m2 + 1 + 1 = R.m := hL.hm.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  rw [← xiOver_eq_XiTop _ _ _ _ _ _ _ _ _ _ hm]
  unfold xiOver
  refine congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ => ?_)
  rw [GlobalTheory.inFr_add, LinearMap.comp_add]
  refine GlobalTheory.GO.locTop_add hL.hm hL.cst_ok (hL.depthQ Q) _ (fun s l => ?_) (hY Q)
  simpa [castSp, LinearMap.funLeft_apply] using h2 Q s (Fin.cast (congrArg R.N hm).symm l)

theorem entry_supp (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1)))
    (hx : XiEntry Ch sel mu cst L i al be p p' x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.xiSupp i hi al be Q _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem entry_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1)) (x y : HomE X.E (R.N i) (R.N (i + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + y) = XiEntry Ch sel mu cst L i al be p p' x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg _ (GlobalTheory.inFr_add _ _ x y)).trans (hL.xiInv i hi al be Q _ _ (h2 Q)))

theorem cpl_supp (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hx : XiCpl1 Ch sel mu cst L m2 al p₀ p Y x ≠ 0) :
    x ∈ divLat (cAof sel mu cst) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N) :=
  GlobalTheory.GO.mem_divLat_of_loc _ _ (left_ne_zero_of_mul hx) fun Q =>
    hL.psiSuppX al Q _ _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) Q (Finset.mem_univ _))

theorem cpl_add (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2)
    (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x y : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + y) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
  obtain ⟨h1, h2⟩ := GlobalTheory.GO.loc_of_mem_mulLat hPr _ _ x hy
  exact congrArg₂ (· * ·) h1 (Finset.prod_congr rfl fun Q _ =>
    (congrArg (fun t => PsiAt Ch sel mu cst m2 Q _ t _) (GlobalTheory.inFr_add _ _ x y)).trans (hL.psiInvX al Q _ _ _ (h2 Q)))

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem transport {D : D7} {X : Fields} (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (S : Finset (HeightOneSpectrum (𝓞 X.E)))
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (f : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin a → D.host.E)) (f' : (Fin b → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E))
    (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) (Ξ : HomE X.E a b → X.K)
    (hAA : ∀ P ∈ S, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 X.E) {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0,
      r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E))
    (h1 : ∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) (h2 : ∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) :
    DatLoc D cc (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (cA * cB)
        ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))
        (fun z => s.σ₀ (Ξ (seamHom s (inFr f f' z)))) ∧
      ∀ z, s.σ₀ (Ξ (seamHom s (inFr f f' z))) ≠ 0 → z ∈ divLat (cA * cB)
        (homAt (S.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding)
          ((s.lat N).map (f.toLinearMap.restrictScalars (𝓞 D.host.E))) ((s.lat N').map (f'.toLinearMap.restrictScalars (𝓞 D.host.E)))) :=
  _root_.GlobalTheory.DatTransport.datLoc_seam_inFr s cc S N N' f f' cA cB hA hB Ξ hAA h1 h2

theorem cosetNonempty {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (fr : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) : ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((fr P).symm y) (y0 P) :=
  _root_.GlobalTheory.FrameCongApprox.exists_sameCoset sel mu cst fr y0

open Classical in
theorem couplingBaseVector_bound_kernelChain {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) :=
  _root_.GlobalTheory.TwU.baseCosetRepresentative_bounded_at_bad_primes A dtU a H β x Q l

open Classical in
theorem cosetBound {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E) (H : AdTie A dtU a)
    (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (x : UA D (t.m2 + 1) hi)
    (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))) :
    IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) l) := by
  have hy0 : ∀ P, y0At A (t.m2 + 1) hi β P = A.y0 β P := fun P => by simp [y0At]
  obtain ⟨y, hy⟩ := cosetNonempty t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) p P) (fun P => A.y0 β P)
  have hne : repY (cosetOf A (t.m2 + 1) hi β p) ∈ cosetOf A (t.m2 + 1) hi β p := by
    unfold repY
    exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p) ⟨y, fun P => by rw [hy0]; exact hy P⟩
  have h1 := hne Q l
  rw [hy0] at h1
  have h2 := couplingBaseVector_bound_kernelChain A dtU a H β x Q l
  generalize (frsF t.sel (t.tup μ) p Q).symm (repY (cosetOf A (t.m2 + 1) hi β p)) = v at h1 ⊢
  rw [Pi.sub_apply] at h1
  have hq := GlobalTheory.TopInv.qOf_ne (E := t.X.E) Q.1
  split_ifs at h1 h2 ⊢ with hQ
  · have e : (qOf Q.1 : t.X.E) ^ 1 * v l = (qOf Q.1 : t.X.E) * (((qOf Q.1 : t.X.E) ^ 0)⁻¹ * (v l - A.y0 β Q l)) +
        (qOf Q.1 : t.X.E) ^ 1 * A.y0 β Q l := by ring
    rw [e]
    exact ((GlobalTheory.TopStep.intAt_nat _).mul h1).add h2
  · have e : (qOf Q.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf Q.1 : t.X.E) ^ (t.cst μ).M * (qOf Q.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf Q.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v l - A.y0 β Q l)) + (qOf Q.1 : t.X.E) ^ (t.cst μ).M * A.y0 β Q l := by
      field_simp
      ring
    rw [e]
    exact (((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _)).mul h1).add h2

set_option maxHeartbeats 800000 in
theorem sizeLaw_of_tie' : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → SizeLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT hPt i hi β β' x x'
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  have hL := t.idx_ok μ
  have hPr := t.pr_ok
  have hp := (hPt i (Nat.le_of_succ_le hi) β x).choose_spec
  have hp' := (hPt (i + 1) hi β' x').choose_spec
  have hxi : xiAd A a i hi β β' x x' = fun z => t.seam.σ₀ (xiPt A i hi β β' (hPt i (Nat.le_of_succ_le hi) β x).choose
      (hPt (i + 1) hi β' x').choose (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) :=
    funext fun z => dif_pos ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  generalize (hPt i (Nat.le_of_succ_le hi) β x).choose = p at hp hxi
  generalize (hPt (i + 1) hi β' x').choose = p' at hp' hxi
  have hS : ssRec t u μ = (Sall t.sel (t.tup μ) (t.word u)).map
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv t.seam.iE)).toEmbedding := by
    unfold ssRec
    rw [hSS]
  rw [hxi, hS, hlev, latK_eq_map _ (A.crd i (Nat.le_of_succ_le hi)), latK_eq_map _ (A.crd (i + 1) hi), ← hp.lat, ← hp'.lat]
  unfold levC
  refine transport t.seam t.cc _ _ _ _ _ _ _ GlobalTheory.GO.twDen_pos (GlobalTheory.GO.twMod_pos (hPr.T_prime _).pos) _
    (fun P hP => hT.aa P hP) ?_ ?_
  · intro z hz
    unfold xiPt at hz
    split_ifs at hz with h1 h2
    · exact entry_supp hL h1 _ _ _ _ z hz
    · subst h2
      exact cpl_supp hL _ _ _ _ z hz
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_supp hL _ _ _ z hz
  · intro z y hy
    unfold xiPt
    split_ifs with h1 h2
    · exact entry_add hPr hL h1 _ _ _ _ z y hy
    · subst h2
      exact cpl_add hPr hL _ _ _ _ z y hy
    · obtain rfl : i = t.m2 + 1 := by have := m_eq t μ; omega
      exact top_add hPr hL _ _ _ (fun Q l => cosetBound A dtU a hT _ β x _ Q l) z y hy

end GlobalTheory.TwV.EntrySupportBounds

theorem GlobalTheory.TwV.sizeLaw_of_tie : GlobalTheory.TwV.UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => GlobalTheory.TwV.PtEx A a → GlobalTheory.TwV.SizeLaw A a) :=
  GlobalTheory.TwV.EntrySupportBounds.sizeLaw_of_tie'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicMatrixCongruentOneAtPrimeMulOfBoth
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CongProd

open _root_.Formalism.L2.Col GlobalTheory.TwU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ _root_.Formalism.L2.Herm.intAf F E := fun x => (_root_.Formalism.L2.DIV.toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul₁ {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int₁ (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (_root_.Formalism.L2.DIV.toRInt F E x).2⟩

theorem intAtA_sum₁ {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int₁ (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add₁ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congAt_mul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (k k' : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))),
    GlobalTheory.TwU.CongAt Q n k → GlobalTheory.TwU.CongAt Q n k' → GlobalTheory.TwU.CongAt Q n (k * k') := by
  intro F E _ _ _ _ _ Q n N k k' h h' a b
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set c := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hc
  set d := iA F E (algebraMap (𝓞 E) E (((qOf Q : ℕ) : 𝓞 E) ^ n)) with hd
  have hcd : d * c = 1 := by
    rw [hc, hd, ← map_mul, map_pow, map_natCast, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have e : ((k * k' : GL (Fin N) _) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      ((k : Matrix (Fin N) (Fin N) _) - 1) * ((k' : Matrix (Fin N) (Fin N) _) - 1) +
        (((k : Matrix (Fin N) (Fin N) _) - 1) + ((k' : Matrix (Fin N) (Fin N) _) - 1)) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply, mul_add, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_add₁ (intAtA_sum₁ _ _ fun l _ => ?_) (intAtA_add₁ (h a b) (h' a b))
  have e2 : ∀ x y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, c * (x * y) = d * ((c * x) * (c * y)) := by
    intro x y
    linear_combination (-(c * (x * y))) * hcd
  rw [e2]
  exact intAtA_mul₁ (intAtA_int₁ _) (intAtA_mul₁ (h a l) (h' l b))

end GlobalTheory.CongProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
section
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.Svd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

def Part.ofBuilt {𝒮 : Slots} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
    {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c) : Part w Z c.O where
  pin := b.pin
  col := b.col.toColT
  errX := b.errX
  tp := b.n.tp
  xi := b.n.xi
  qp := b.div.Qp
  ker0 := b.ker0
  ker_eq := b.ker_eq
  ker := b.ker

theorem builtC_hasPart : ∀ (𝒮 : Slots), (∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c) ∧
    ∀ K X f T c, IsBuilt 𝒮 K X f T c → positionOf HasPart K X f T c := fun 𝒮 =>
  have h : ∀ K B f T w Z c, BuiltC 𝒮 K B f T w Z c → HasPart K B f T w Z c := fun _ _ _ _ _ _ _ ⟨b⟩ => ⟨Part.ofBuilt b⟩
  ⟨h, fun K X f T c hc => positionOf_mono h K X f T c hc⟩

end GlobalTheory.Svd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {w : Pr.Word}


open Classical in
theorem cplCoset_frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · have h1 : p.deco.1.HasLift ⟨P.1, h⟩ := Deco.Ok.hasLift p.deco.2 ⟨P.1, h⟩
    exact (Deco.liftFr_spec h1).1 x
  · exact Subtype.property p ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

theorem cplCoset_sameCoset_of_common {cst : LocCst X (rowSG Pr sel mu)} {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n}
    (h : SameCoset sel mu cst P x z) (h' : SameCoset sel mu cst P y z) : SameCoset sel mu cst P x y := fun l => by
  have h1 := (h l).add (ciIntAt_neg (h' l))
  rwa [← mul_neg, ← Pi.neg_apply, ← mul_add, ← Pi.add_apply, neg_sub, sub_add_sub_cancel] at h1

end Gen

end GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem cplCoset_bound : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  classical
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP H hi β P y hy
  obtain ⟨⟨c, rfl⟩, -⟩ := ((St (t.m2 + 1) hi).K β).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨y1, hy1, hY⟩ := H.chain.2.1 c
  have hmem : y1 ∈ A.yb c := by rw [hY]; simp
  have h0 := H.coset c y1 hmem P
  have hy' : SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P) := by
    unfold y0At at hy
    rwa [dite_eq_left rfl] at hy
  have hyw := cplCoset_sameCoset_of_common t.sel (t.tup μ) hy' h0
  set p := A.pt (t.m2 + 1) (cpl_lt t μ).le c with hp
  set w := (frsF t.sel (t.tup μ) p P).symm y1 with hw
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hloc := (mem_locLat _ _ _ _).1 hy1 P
  have hw1 : ∀ l, IntAt P.1 ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) * w l) := by
    have h2 : frsF t.sel (t.tup μ) p P ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) • w) ∈ p.deco.1.at P.1 := by
      rw [map_smul, hw, LinearEquiv.apply_symm_apply]
      exact hloc
    have h3 := (ciMem_stdAt _ _).1 ((cplCoset_frsF_mem t.sel (t.tup μ) p P _).1 h2)
    intro l
    simpa using h3 l
  refine ⟨fun hG l => ?_, fun hG l => ?_⟩
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_true, pow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, Pi.sub_apply] at h1 h2
    have e : (qOf P.1 : t.X.E) * y l = (qOf P.1 : t.X.E) * (y l - w l) + (qOf P.1 : t.X.E) * w l := by ring
    rw [e]
    exact (ciIntAt_q.mul h2).add h1
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_false, _root_.zpow_neg, zpow_natCast, inv_inv, Pi.sub_apply] at h1 h2
    have hqM : IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M) := by
      have := IntAt.coe P.1 (((qOf P.1 ^ (t.cst μ).M : ℕ)) : 𝓞 t.X.E)
      rwa [map_natCast, Nat.cast_pow] at this
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * y l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (y l - w l)) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * w l := by
      field_simp
      ring
    rw [e]
    exact ((hqM.mul hqM).mul h2).add h1

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointAdelicRightMulLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.PtMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (κ : ((St i hi).K β).lev.U) (x x₁ : UA D i hi)
    (p q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (k : SB t μ → (Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i))),
    x₁.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → q.deco.1.N = p.deco.1.N → q.deco.1.f = p.deco.1.f →
    (∀ P, frsF t.sel (t.tup μ) q P = frsF t.sel (t.tup μ) p P * k P) → (∀ P, k P ∈ GLint t.X.E (D.R.N i) P.1) →
    (∀ P, InFrame t.seam (A.fb i hi β) (t.cst μ).D P κ.1 (k P)) → IsPtAd A a i hi β x₁ q) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi β κ x x₁ p q k hx hp hN hf hfr hk hin
  refine ⟨?_, ?_, ?_⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab x.1 κ.1 _ (hatStab_of_lev _ κ)]
  · intro P
    have e1 : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
        (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; group
    rw [e1, hfr P, map_mul (seamGL t.seam)]
    exact GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) (hin P) (GlobalTheory.CplPt.seamGL_int t.seam ⟨k P, hk P⟩)
  · intro P v h hv
    have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x.1) p.deco.1 κ (hp.fnl P v h hv)
    have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by rw [hx, mul_assoc]
    rw [e]
    intro w hw z hz
    have H2 := H w (hN ▸ hw) z hz
    rw [hf]
    exact H2

end GlobalTheory.PtMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hj : t.m2 + 1 ≤ D.R.m) (β' : (St (t.m2 + 1) hj).Ch)
    (x' x₁' : UA D (t.m2 + 1) hj) (κ' : ((St (t.m2 + 1) hj).K β').lev.U) p', x₁'.1 = x'.1 * κ'.1 → IsPtAd A a (t.m2 + 1) hj β' x' p' →
    ∃ (q' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (κ'' : GLQ t.X.E (D.R.N (t.m2 + 1)) (SB t μ)),
      IsPtAd A a (t.m2 + 1) hj β' x₁' q' ∧
      (∀ (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) t.m2) w, phiT t.X.K p.deco.1 q'.deco.1 w = phiT t.X.K p.deco.1 p'.deco.1 w) ∧
      (∀ P, frsF t.sel (t.tup μ) q' P = frsF t.sel (t.tup μ) p' P * ((κ'' P)⁻¹).1) ∧
      ∀ P, InFrame t.seam (A.fb (t.m2 + 1) hj β') (t.cst μ).D P κ'.1 ((κ'' P)⁻¹).1) := by
  first | exact @GlobalTheory.CplPt.ptAd_levCpl | exact GlobalTheory.CplPt.ptAd_levCpl | (intros; apply GlobalTheory.CplPt.ptAd_levCpl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilled
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwU.AtTrue.charts_funKilled_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K0 hK hfin
  obtain ⟨K', hK', hprop⟩ := TC.charts_funKilled I hI hP l Z u a i hi bad Ch chOf K0 hK
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.TwU.AtTrue.readsMove_holds I hI hP l Z u a i hi bad Ch chOf K' hK'
  refine ⟨fun β => moveChart (K' β) (k β), hk, fun β => ⟨(hprop β).1, ?_⟩⟩
  obtain ⟨hF, -, -, hU, hchi, -, -⟩ := hprop β
  obtain ⟨n, hn, hn'⟩ := hfin β
  refine ⟨n, hn, fun κ => ?_⟩
  have hm : (k β).1 * κ.1 * (k β).1⁻¹ ∈ (K0 β).lev.U := hU ▸ κ.2
  show ((K' β).lev.chi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩) ^ n = 1
  have e := hchi ⟨(k β).1 * κ.1 * (k β).1⁻¹, κ.2⟩ ⟨_, hm⟩ rfl
  exact e.symm ▸ hn' _
end

