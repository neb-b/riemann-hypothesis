module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueIsometryFixingBothFramesOfFrameAdapt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameActionMulEquivFiniteAdelicUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCoset
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7} {T T' : D.host.E}

theorem mul_mem_isometriesFixingBothFrames {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'} {h k : GV D} (hh : h ∈ H0 F F')
    (hk : k ∈ H0 F F') : h * k ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hh.1 hk.1, fun a => by rw [le_mul_app, hk.2.1 a, hh.2.1 a],
    fun a => by rw [le_mul_app, hk.2.2 a, hh.2.2 a]⟩

theorem principalPolarisation_exists_unique_section (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') : (1 : GV D) ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun _ => rfl, fun _ => rfl⟩

theorem nlam_iff_nrat {F0 : LFlag (D.sp.Y 0) D.R.rS T} {lam : LV D} {b : GV D} (hb : b ∈ Aut0 F0 lam) :
    b ∈ NLam lam F0 ↔ b ∈ NRat F0 :=
  ⟨fun h => ⟨h.1.1, h.2.1, h.2.2⟩, fun h => ⟨⟨h.1, hb.2⟩, h.2.1, h.2.2⟩⟩

section Corr

variable {F0 F : LFlag (D.sp.Y 0) D.R.rS T} {F0' F' : LFlag (D.sp.Y 0) D.R.rS T'} {γ g : GV D}

theorem s_adapt (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
    {b₁ b₂ n n' : GV D} (hb1 : Adapt b₁ F0 F0) (hb2 : Adapt b₂ F0' F0') (hn : n ∈ NRat F0) (hn' : n' ∈ NRat F0')
    (he : b₁ * γ * b₂⁻¹ = n * γ * n') :
    Adapt (g * n⁻¹ * b₁ * g⁻¹) F F ∧ Adapt (g * n⁻¹ * b₁ * g⁻¹) F' F' ∧
      g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
  have e1 : n⁻¹ * b₁ = γ * n' * b₂ * γ⁻¹ := by
    calc n⁻¹ * b₁ = n⁻¹ * (b₁ * γ * b₂⁻¹) * b₂ * γ⁻¹ := by group
      _ = n⁻¹ * (n * γ * n') * b₂ * γ⁻¹ := by rw [he]
      _ = γ * n' * b₂ * γ⁻¹ := by group
  have hseq : g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
    calc g * n⁻¹ * b₁ * g⁻¹ = g * (n⁻¹ * b₁) * g⁻¹ := by group
      _ = g * (γ * n' * b₂ * γ⁻¹) * g⁻¹ := by rw [e1]
      _ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by group
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  refine ⟨adapt_mul (adapt_inv hg) (adapt_mul hb1 (adapt_mul (adapt_nrat (nrat_inv hn)) hg)), ?_, hseq⟩
  rw [hseq]
  exact adapt_mul (adapt_inv hG) (adapt_mul (adapt_mul hb2 (adapt_nrat hn')) hG)

theorem cong_mod {A0 A : LFlag (D.sp.Y 0) D.R.rS T} {a s μ n b : GV D} (ha : Adapt a A0 A) (hs : Adapt s A A)
    (hμ : μ ∈ NRat A) (hn : n ∈ NRat A0) (hb : Adapt b A0 A0) (hseq : s = a * (n * b) * a⁻¹) :
    ∀ x ∈ orth (VS D) (Xsp A), (s * μ⁻¹) x - (a * b * a⁻¹) x ∈ Xsp A := by
  intro x hx
  have e : (s * μ⁻¹) x - (a * b * a⁻¹) x = s (μ⁻¹ x - x) + a (n (b (a⁻¹ x)) - b (a⁻¹ x)) := by
    rw [hseq]
    simp only [le_mul_app, map_sub]
    abel
  rw [e]
  refine add_mem (mem_of_map_eq (adapt_xsp hs) ((nrat_inv hμ).2.2 x hx)) ?_
  refine mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ ?_)
  exact mem_of_map_eq (adapt_orth hb) (symm_mem_of_map_eq (adapt_orth ha) hx)

variable (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
  (hI : ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F')
include hγ hg hg'

include hI in
theorem corr_exists {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) :
    ∃ h, Corr F0 F F0' F' γ g b h := by
  obtain ⟨⟨n, hn, n', hn', he⟩, -⟩ := hb.2.2
  obtain ⟨hs1, hs2, -⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  obtain ⟨h, ⟨hh, h1, h2⟩, -⟩ := hI _ hs1 hs2
  exact ⟨h, hh, n, hn, n', hn', he, h1, h2⟩

include hI in
theorem corr_unique {b : GV D × GV D} (hb1 : Adapt b.1 F0 F0) (hb2 : Adapt b.2 F0' F0') {h k : GV D}
    (hh : Corr F0 F F0' F' γ g b h) (hk : Corr F0 F F0' F' γ g b k) : h = k := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', he2, k1, k2⟩ := hk
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb1 hb2 hn hn' he
  obtain ⟨-, -, hteq⟩ := s_adapt hγ hg hg' hb1 hb2 hm hm' he2
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have tF : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (g * b.1⁻¹) * (m * n⁻¹) * (g * b.1⁻¹)⁻¹ := by group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb1) hg) (nrat_mul hm (nrat_inv hn))
  have tF' : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F' := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) =
        ((g * γ) * b.2⁻¹) * (m'⁻¹ * n') * ((g * γ) * b.2⁻¹)⁻¹ := by rw [hseq, hteq]; group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb2) hG) (nrat_mul (nrat_inv hm') hn')
  obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
  have ek : k⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (k⁻¹ * (g * m⁻¹ * b.1 * g⁻¹)) * ((g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) := by group
  rw [hu h ⟨hh0, h1, h2⟩, hu k ⟨hk0, by rw [ek]; exact nrat_mul k1 tF, by rw [ek]; exact nrat_mul k2 tF'⟩]

theorem corr_mul {lam lam' : LV D} {b c : GV D × GV D} (hb : InB F0 F0' lam lam' γ b)
    (hc : InB F0 F0' lam lam' γ c) {h k : GV D} (hh : Corr F0 F F0' F' γ g b h)
    (hk : Corr F0 F F0' F' γ g c k) : Corr F0 F F0' F' γ g (b * c) (h * k) := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', hec, k1, k2⟩ := hk
  have hk1 := (frameAdaptedIsometry_of_fixing_both_frames hk0).1
  have hk2 := (frameAdaptedIsometry_of_fixing_both_frames hk0).2
  refine ⟨mul_mem_isometriesFixingBothFrames hh0 hk0, b.1 * m * b.1⁻¹ * n, nrat_mul (nrat_conj hb.1.1 hm) hn,
    n' * (b.2 * m' * b.2⁻¹), nrat_mul hn' (nrat_conj hb.2.1.1 hm'), ?_, ?_, ?_⟩
  · show b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = _
    calc b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = b.1 * (c.1 * γ * c.2⁻¹) * b.2⁻¹ := by group
      _ = b.1 * (m * γ * m') * b.2⁻¹ := by rw [hec]
      _ = b.1 * m * b.1⁻¹ * (b.1 * γ * b.2⁻¹) * (b.2 * m' * b.2⁻¹) := by group
      _ = b.1 * m * b.1⁻¹ * (n * γ * n') * (b.2 * m' * b.2⁻¹) := by rw [he]
      _ = _ := by group
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk1) h1) k1
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk2) h2) k2

theorem corr_stab {lam lam' Λ : LV D} (hγl : Formalism.HermitianLatticesTheory.gmap γ lam' = lam) (hΛ : Λ = Formalism.HermitianLatticesTheory.gmap g lam)
    {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D} (hh : Corr F0 F F0' F' γ g b h) :
    h ∈ stabL F F' Λ := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have hh' : h = (g * n⁻¹ * b.1 * g⁻¹) * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹))⁻¹ := by group
  refine ⟨hh0, (_root_.GlobalTheory.GdatIota.gdat_iff_iotaCompat D T T' F0 F F0' F' lam lam' Λ γ g h b.1 b.2 hγ hγl hg hg' hΛ hb.1 hb.2.1 hh0
    ?_ ?_).2 hb.2.2.2⟩
  · intro x hx
    rw [hh']
    exact cong_mod hg hs1 h1 (nrat_inv hn) hb.1.1 (by group) x hx
  · intro x hx
    rw [hh', show g * γ * b.2 * γ⁻¹ * g⁻¹ = (g * γ) * b.2 * (g * γ)⁻¹ by group]
    exact cong_mod hG hs2 h2 hn' hb.2.1.1 hseq x hx

include hI in
theorem corr_ker {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D}
    (hh : Corr F0 F F0' F' γ g b h) : h = 1 ↔ b.1 ∈ NLam lam F0 ∧ b.2 ∈ NLam lam' F0' := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  rw [nlam_iff_nrat hb.1, nlam_iff_nrat hb.2.1]
  constructor
  · rintro rfl
    rw [inv_one, one_mul] at h1 h2
    constructor
    · have c := nrat_conj (adapt_inv hg) h1
      have e : g⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) * g⁻¹⁻¹ = n⁻¹ * b.1 := by group
      rw [e] at c
      have := nrat_mul hn c
      rwa [mul_inv_cancel_left] at this
    · rw [hseq] at h2
      have c := nrat_conj (adapt_inv hG) h2
      have e : (g * γ)⁻¹ * ((g * γ) * (n' * b.2) * (g * γ)⁻¹) * (g * γ)⁻¹⁻¹ = n' * b.2 := by group
      rw [e] at c
      have := nrat_mul (nrat_inv hn') c
      rwa [inv_mul_cancel_left] at this
  · rintro ⟨c1, c2⟩
    have sF : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F := by
      have e : g * n⁻¹ * b.1 * g⁻¹ = g * (n⁻¹ * b.1) * g⁻¹ := by group
      rw [e]; exact nrat_conj hg (nrat_mul (nrat_inv hn) c1)
    have sF' : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F' := by
      rw [hseq]; exact nrat_conj hG (nrat_mul hn' c2)
    obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
    rw [hu h ⟨hh0, h1, h2⟩, hu 1 ⟨principalPolarisation_exists_unique_section F F', by rwa [inv_one, one_mul], by rwa [inv_one, one_mul]⟩]

end Corr

theorem card_of_hom {G : Type*} [Group G] {B : Subgroup (G × G)} {N N' : Subgroup G} (φ : B →* G) (S : Set G)
    (hR : ∀ h, h ∈ φ.range ↔ h ∈ S) (hK : ∀ b : B, φ b = 1 ↔ (b : G × G).1 ∈ N ∧ (b : G × G).2 ∈ N') :
    Nat.card S = (N.prod N').relIndex B := by
  have hker : φ.ker = (N.prod N').subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_prod, hK]
  have e1 : Nat.card S = Nat.card φ.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun h => (hR h).symm)
  rw [e1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, Subgroup.relIndex, ← hker]
  rfl

theorem stab_card : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  intro D X Y u u' F F' w hZ hG t Λ hTG B N N' hB hN hN'
  obtain ⟨g, hg, hg', hΛ⟩ := hTG
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hg2 : Adapt g (mapLF t.lin (lf D (X.Fu u'))) F' := hg'
  have hI := _root_.GlobalTheory.Unfold.Inter.common_stabiliser D X Y u u' F F' w hZ hG
  have hB' : ∀ b, b ∈ B ↔ InB (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lam' t.lin b := hB
  have hf : ∀ b : B, ∃ h, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) h :=
    fun b => corr_exists hγ hg hg2 hI ((hB' b).1 b.2)
  let f : B → GV D := fun b => Classical.choose (hf b)
  have hfs : ∀ b : B, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) (f b) :=
    fun b => Classical.choose_spec (hf b)
  have hAd : ∀ b : B, Adapt (b : GV D × GV D).1 (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Adapt (b : GV D × GV D).2 (lf D (X.Fu u')) (lf D (X.Fu u')) :=
    fun b => ⟨((hB' b).1 b.2).1.1, ((hB' b).1 b.2).2.1.1⟩
  let φ : B →* GV D := MonoidHom.mk' f fun b c =>
    corr_unique hγ hg hg2 hI (hAd (b * c)).1 (hAd (b * c)).2 (hfs (b * c))
      (corr_mul hγ hg hg2 ((hB' b).1 b.2) ((hB' c).1 c.2) (hfs b) (hfs c))
  refine card_of_hom φ _ (fun h => ⟨?_, fun hh => ?_⟩) (fun b => ?_)
  · rintro ⟨b, rfl⟩
    exact corr_stab hγ hg hg2 hγl hΛ ((hB' b).1 b.2) (hfs b)
  · have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
    have hrow' : IsRowLat D (X.Fu u') t.lam' := (Y.rowsOK u').1 _ t.mem'
    obtain ⟨b, hbB, hbC⟩ := _root_.GlobalTheory.StabCnt.stab_onto D _ _ (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lam t.lam' Λ t.lin g h
      hγ hγl hg hg2 hΛ (fun σ hσ hL => _root_.GlobalTheory.Unfold.sameInner_unip D _ (X.Fu u) t.lam t.lam σ hrow hrow hσ hL)
      (fun σ hσ hL => _root_.GlobalTheory.Unfold.sameInner_unip D _ (X.Fu u') t.lam' t.lam' σ hrow' hrow' hσ hL) hh
    refine ⟨⟨b, (hB' b).2 hbB⟩, ?_⟩
    exact corr_unique hγ hg hg2 hI hbB.1.1 hbB.2.1.1 (hfs _) hbC
  · have hK := corr_ker hγ hg hg2 hI ((hB' b).1 b.2) (hfs b)
    show f b = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show _ ∈ (N : Set (GV D)); rw [hN]; exact h1
      · show _ ∈ (N' : Set (GV D)); rw [hN']; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : (b : GV D × GV D).1 ∈ (N : Set (GV D)) := h1
        rwa [hN] at this
      · have : (b : GV D × GV D).2 ∈ (N' : Set (GV D)) := h2
        rwa [hN'] at this

end GlobalTheory.StabCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatch
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDict_bij_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  intro D X u F Tr hK hσ hL
  obtain ⟨hψ, -, hEq, hDet, hOnto⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨hJinj, hJsurj⟩ := _root_.GlobalTheory.transport_J_bijective_onto D X u F Tr
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have hcls := (_root_.GlobalTheory.ColClass.classes_and_weight D X u F Tr hK hσ hL).1
    have h1 : ∀ c, shP X u T.1 (Tr.hc c) = 0 := by
      intro c
      apply hJinj
      rw [map_zero]
      funext y
      have := congrFun (congrFun hT c) (F.val0.eY.symm y)
      simpa [colDictL, dictA] using this
    apply hDet T
    intro x
    obtain ⟨c, ⟨γ, κ, hx⟩, -⟩ := hcls x
    rw [hx, hEq, h1, map_zero, smul_zero]
  · intro φ hφ
    rw [Formalism.L2.Forms.Mu0_iff F.val0] at hφ
    obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hφ
    obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.frame_action_mulEquiv D X u Tr.wt Tr.ιA hW hA hσ
    obtain ⟨hΓ, -, hs⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
    have hKm : ∀ h : Hfin X u, h ∈ Ku X u hK ↔ ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U :=
      fun h => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).1
    have hχ : ∀ (h : Hfin X u) (hk : h ∈ Ku X u hK) (hy : ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U), ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) :=
      fun h hk hy => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).2 hk hy
    have hπ : ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E),
        (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g →
        ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
          Formalism.L2.Forms.IsTr (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1) y' y →
          Tr.J (piRep X u (iotaI X u γ) ξ) y = Tr.J ξ y' := by
      intro γ g e ξ y y' hy
      have h2 := hs γ g e
      exact Tr.J_eqv (iotaI X u γ) (iotaI X u γ).2 ξ y y' (by rw [h2]; exact hy)
    rw [Formalism.L2.Forms.lamT_zero] at hJsurj
    obtain ⟨φ', hφ'eq, hφ'g⟩ := GlobalTheory.adForm_from_equivariant _ _ (Formalism.L2.Forms.sigD D) _ _ _ _ _ F.cls0.lev
      (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 _
      (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ hKm hχ hΓ hπ hJinj hJsurj g hg
    obtain ⟨T, hT⟩ := hOnto φ' hφ'eq
    refine ⟨T, ?_⟩
    funext c z
    have hc : Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := (hΦ _ _).1 (Tr.hc_rep c)
    have e1 := congrFun (congrFun hres c) (F.val0.eY z)
    have e2 := hφ'g (F.cls0.y c)
    have e3 : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c := (MulEquiv.symm_apply_eq Φ).2 hc.symm
    rw [e3] at e2
    show Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY z) = φ c z
    rw [hT, ← e2]
    simpa [Formalism.L2.Forms.res] using e1

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeAlongLieAlgebraPreservesSmoothSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerClosedSmooth

open GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.Lift

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exists_coords {n : ℕ} (S : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (m : ℕ) (e : Fin m → Matrix (Fin n) (Fin n) ℂ) (c : Fin m → Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ), (∀ j, e j ∈ S) ∧
      ∀ {A : Type} (L : Matrix (Fin n) (Fin n) ℂ → A → ℂ),
        (∀ (a : ℝ), ∀ X ∈ S, ∀ Y ∈ S, L (a • X + Y) = (a : ℂ) • L X + L Y) →
        ∀ Y ∈ S, ∀ x, L Y x = ∑ j, (c j Y : ℂ) * L (e j) x := by
  let b := Module.finBasis ℝ S
  choose c hc using fun j => LinearMap.exists_extend (b.coord j)
  refine ⟨_, fun j => b j, fun j => LinearMap.toContinuousLinearMap (c j), fun j => (b j).2, fun L hL Y hY x => ?_⟩
  have h0 : L 0 = 0 := by
    have := hL 1 0 S.zero_mem 0 S.zero_mem
    simpa using this
  let l : S →ₗ[ℝ] ℂ :=
    { toFun := fun Z => L Z x
      map_add' := fun Z Z' => by simpa using congrFun (hL 1 Z Z.2 Z' Z'.2) x
      map_smul' := fun a Z => by simpa [h0] using congrFun (hL a Z Z.2 0 S.zero_mem) x }
  have h1 : L Y x = l ⟨Y, hY⟩ := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← b.sum_repr ⟨Y, hY⟩, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : c j Y = b.repr ⟨Y, hY⟩ j := LinearMap.congr_fun (hc j) ⟨Y, hY⟩
  rw [map_smul, LinearMap.coe_toContinuousLinearMap', h2, Complex.real_smul]
  rfl

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}


variable (V) in
def lieSub (τ : D.what₂.Tau) : Submodule ℝ (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  GlobalTheory.UnitaryLieAlgebra.unitaryLie (gramAt D V τ)


variable (θ) in
def SmFam {k : ℕ} (B : (Fin k → ℝ) → GA D V) : Prop :=
  ∀ τ, (ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)) ∧
    ContDiff ℝ ∞ fun t => infMat D.sp.cm.sig V.gram (θ τ) (B t)⁻¹

theorem SmFam.mul {k : ℕ} {A B : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) (hB : SmFam θ B) :
    SmFam θ fun t => A t * B t := fun τ => by
  simp only [_root_.mul_inv_rev, infMat_mul]
  exact ⟨(hA τ).1.mul (hB τ).1, (hB τ).2.mul (hA τ).2⟩

theorem SmFam.tail {k : ℕ} {A : (Fin k → ℝ) → GA D V} (hA : SmFam θ A) :
    SmFam θ fun t : Fin (k + 1) → ℝ => A (Fin.tail t) := fun τ => by
  have h : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.tail t := contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ => ℝ) i.succ
  exact ⟨(hA τ).1.comp h, (hA τ).2.comp h⟩

theorem contDiff_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) :
    ContDiff ℝ ∞ fun s : ℝ => infMat D.sp.cm.sig V.gram (θ τ') (oneP θ V τ X s) := by
  by_cases c : τ' = τ
  · subst c
    simp only [(isAtTau_oneP hθ hX _).2.1]
    have h2 : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t := contDiff_pi.2 fun _ => contDiff_id
    simpa [Function.comp_def] using (GlobalTheory.GardingVec.contDiff_expProd fun _ : Fin 1 => X).comp h2
  · simp only [(isAtTau_oneP hθ hX _).2.2 τ' c]
    exact contDiff_const

theorem smFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {k : ℕ} (i : Fin k) : SmFam θ fun t : Fin k → ℝ => oneP θ V τ X (t i) := fun τ' => by
  have hi : ∀ t, (oneP θ V τ X t)⁻¹ = oneP θ V τ X (-t) := fun t => inv_eq_of_mul_eq_one_right (by
    rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ])
  simp only [hi]
  exact ⟨(contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ (fun _ => ℝ) i),
    (contDiff_oneP hθ hX τ').comp (contDiff_apply ℝ (fun _ => ℝ) i).neg⟩


variable (θ) in
def prodP {k : ℕ} (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : Fin k → ℝ) :
    GA D V := (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod

theorem prodP_succ {k : ℕ} (τs : Fin (k + 1) → D.what₂.Tau) (Xs : Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t : Fin (k + 1) → ℝ) : prodP θ τs Xs t =
      oneP θ V (τs 0) (Xs 0) (t 0) * prodP θ (Fin.tail τs) (Fin.tail Xs) (Fin.tail t) := by
  unfold prodP
  rw [List.ofFn_succ, List.prod_cons]
  rfl

theorem prodP_laws (hθ : IsInfFam θ) {k : ℕ} (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hX : ∀ i, Xs i ∈ lieAt V (τs i)) :
    SmFam θ (prodP θ τs Xs) ∧ Continuous (prodP θ τs Xs) ∧ ∀ i, ∃ B : (Fin k → ℝ) → GA D V, SmFam θ B ∧ ∀ t s,
      prodP θ τs Xs (Function.update t i (t i + s)) =
        prodP θ τs Xs t * oneP θ V (τs i) (adAt θ (B t) (τs i) (Xs i)) s := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  induction k with
  | zero =>
    have e : prodP θ τs Xs = fun _ => 1 := funext fun t => by simp [prodP]
    rw [e]
    exact ⟨fun _ => ⟨contDiff_const, contDiff_const⟩, continuous_const, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih (Fin.tail τs) (Fin.tail Xs) fun i => hX i.succ
    rw [funext (prodP_succ (θ := θ) τs Xs)]
    refine ⟨(smFam_oneP hθ (hX 0) 0).mul h1.tail, ((continuous_oneP hθ (hX 0)).comp (continuous_apply 0)).mul
      (h2.comp (continuous_pi fun i => continuous_apply i.succ)), fun i => ?_⟩
    refine Fin.cases ⟨_, h1.tail, fun t s => ?_⟩ (fun j => ?_) i
    · simp only [Function.update_self, Fin.tail_update_zero]
      rw [oneP_add hθ (hX 0), mul_assoc, GlobalTheory.Size.oneP_mul_adelic hθ _ (hX 0) s, mul_assoc]
    · obtain ⟨B, hB, h⟩ := h3 j
      refine ⟨_, hB.tail, fun t s => ?_⟩
      simp only [Fin.tail_update_succ, Function.update_of_ne (Fin.succ_ne_zero j).symm]
      rw [mul_assoc]
      exact congrArg _ (h (Fin.tail t) s)

theorem smooth_of_closed : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam θ → ∀ W : Set (GA D V → ℂ), (∀ f ∈ W, Continuous f ∧ ∀ τ, ∃ L : Matrix (Fin V.rank) (Fin V.rank) ℂ → GA D V → ℂ, (∀ X ∈ lieAt V τ, L X ∈ W ∧ ∀ x, HasDerivAt (fun t : ℝ => f (x * oneP θ V τ X t)) (L X x) 0) ∧ ∀ (a : ℝ), ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ, L (a • X + Y) = (a : ℂ) • L X + L Y) → ∀ f ∈ W, ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod) := by
  intro D θ V hθ W hW f hf k τs Xs hX g
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨-, hc, hP⟩ := prodP_laws hθ τs Xs hX
  choose B hB hP using hP
  suffices h : ∀ n : ℕ, ∀ f ∈ W, ContDiff ℝ n fun t => f (g * prodP θ τs Xs t) from
    contDiff_infty.2 fun n => h n f hf
  intro n
  induction n with
  | zero => exact fun f hf => contDiff_zero.2 ((hW f hf).1.comp (continuous_const.mul hc))
  | succ n ih =>
    intro f hf
    choose L hL hlin using (hW f hf).2
    let d : Fin k → (Fin k → ℝ) → ℂ := fun i t => L (τs i) (adAt θ (B i t) (τs i) (Xs i)) (g * prodP θ τs Xs t)
    have hm : ∀ i t, adAt θ (B i t) (τs i) (Xs i) ∈ lieAt V (τs i) := fun i t =>
      GlobalTheory.Size.adAt_mem_lieAt hθ _ (hX i)
    have hd : ∀ i, ContDiff ℝ n (d i) := fun i => by
      obtain ⟨m, e, c, he, hs⟩ := exists_coords (lieSub V (τs i))
      have e1 : d i = fun t => ∑ j, (c j (adAt θ (B i t) (τs i) (Xs i)) : ℂ) * L (τs i) (e j) (g * prodP θ τs Xs t) :=
        funext fun t => hs _ (hlin (τs i)) _ (hm i t) _
      have e2 : ContDiff ℝ n fun t => adAt θ (B i t) (τs i) (Xs i) :=
        (((hB i (τs i)).2.mul contDiff_const).mul (hB i (τs i)).1).of_le (by exact_mod_cast le_top)
      rw [e1]
      exact ContDiff.sum fun j _ => (Complex.ofRealCLM.contDiff.comp ((c j).contDiff.comp e2)).mul
        (ih _ (hL _ _ (he j)).1)
    have hder := _root_.GlobalTheory.hasFDerivAt_of_continuous_partials k (fun t => f (g * prodP θ τs Xs t)) d (fun i t => by
      have h1 := HasDerivAt.comp_sub_const (t i) (t i) (by rw [sub_self]; exact (hL _ _ (hm i t)).2 (g * prodP θ τs Xs t))
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [mul_assoc, ← hP, add_sub_cancel]) fun i => (hd i).continuous
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ContDiff.sum fun i _ => contDiff_const.smulRight (hd i), hder⟩

end GlobalTheory.DerClosedSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusCommutesWithUnipotentStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_commutes_with_unipotent : Hyps → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetup.exists_setup_both | exact GlobalTheory.Amp.LocalSetup.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetup.exists_setup_both <;> assumption)
end

