module

public import Formalism.LocalToGlobal.Columns.Bundle0025
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Columns.Bundle0023
public import Formalism.LocalToGlobal.Columns.RowFormsGood

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.HermOwed
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

structure AtTOwed (hS : SpStd d.toColBase) (hH : HostHyp d) where
  disc : ∀ u, AtTDisc (d.colRec a) u
  moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)
  xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)

def hermAtT (hS : SpStd d.toColBase) (hH : HostHyp d) (O : AtTOwed a hS hH) (u : d.what₂.Word) :
    CH.AtT (d.colRec a) u (tieEV d.sp.cm d.hX d.hPr u) (fun v => tieFv d.sp.cm d.hX d.hPr u v) :=
  atTOf (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) (fun v => tieFv d.sp.cm d.hX d.hPr u v)
    (fun v x => tieFv_mk d.sp.cm d.hX d.hPr u v x) (th_seen a hH u) (O.disc u) (O.moves u) (O.xp u)

section Asm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
  (O : AtTOwed a hS hH)

end Asm

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtHeckeKv
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Kv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n]

def mhlKv (v : HeightOneSpectrum (𝓞 F)) : Subgroup (UAd hc n) where
  carrier := {η | (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) ∧
    bc (prV (E := E) v) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))}
  one_mem' := ⟨fun w _ => by rw [OneMemClass.coe_one, map_one], by rw [OneMemClass.coe_one, map_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [Subgroup.coe_mul, map_mul, ha1 w hw, hb1 w hw, mul_one]
    · rw [Subgroup.coe_mul, map_mul]; exact mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun w hw => ?_, ?_⟩
    · rw [InvMemClass.coe_inv, map_inv, ha1 w hw, inv_one]
    · rw [InvMemClass.coe_inv, map_inv]; exact inv_mem ha2

variable {hc n}

theorem mhl_eq_put {v : HeightOneSpectrum (𝓞 F)} {η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hη : η ∈ UAd hc n)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) :
    η = rll_put n v (bc (prV (E := E) v) η) := by
  have h1 : (afsplitE hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩).2 = 1 :=
    (afsplitE_snd_eq_one hc.sig 1 v ⟨η, hη⟩).2 h
  have h2 : afsplitU v 1 η = 1 := by
    rw [← afsplitE_snd hc.sig (1 : Matrix (Fin n) (Fin n) E) v ⟨η, hη⟩]
    exact congrArg Subtype.val h1
  conv_lhs => rw [← afsplit_left v η, h2]
  rfl

variable (ST SG : Finset (Pl E))

theorem put_mem_kOne_of_not_over {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {g : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hU : rll_put n v g ∈ UAd hc n)
    (hg : g ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))) : rll_put n v g ∈ K1 hc n ST SG := by
  have hS := rll_put_mem_St n v hg
  have hJ : rll_put n v g ∈ J0 hc n ST := by
    refine ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => ?_⟩
    refine ⟨⟨rll_put n v g, hS⟩, ?_, rfl⟩
    show redAt 1 P ⟨rll_put n v g, hS⟩ ∈ mirab (kP P) n
    rw [rll_put_red n v g hS P (hST P hP)]
    exact one_mem _
  refine ⟨⟨_, hJ⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
  funext w
  exact rll_put_red n v g hS w.1 (hSG w.1 w.2)

theorem localLevel_le_kOne {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    {η : UAd hc n} (hη : η ∈ mhlKv hc n v) : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG := by
  have e := mhl_eq_put η.2 hη.1
  rw [e] at ⊢
  exact put_mem_kOne_of_not_over ST SG hST hSG (e ▸ η.2) hη.2

theorem decoOf_mul_mhlKv {v : HeightOneSpectrum (𝓞 F)} (hST : ∀ P ∈ ST, ¬ IsOver v P) (hSG : ∀ P ∈ SG, ¬ IsOver v P)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {η : UAd hc n} (hη : η ∈ mhlKv hc n v) :
    decoOf ST SG (x * (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) = decoOf ST SG x :=
  decoration_mul_principal hc n ST SG x (localLevel_le_kOne ST SG hST hSG hη)

theorem mem_localLevel_of_mem_kOne {v : HeightOneSpectrum (𝓞 F)} {η : UAd hc n}
    (h1 : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hK : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ K1 hc n ST SG) : η ∈ mhlKv hc n v := by
  refine ⟨h1, ?_⟩
  have hS : (η : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    congruence_subgroup_le_stabilizer hc n ST (principal_le_congruence_subgroup hc n ST SG hK)
  rw [St_one] at hS
  exact Formalism.L2.DIV.lc_stab_loc v (stdLat E n) _ hS

theorem mhl_inv_mul_mem {v : HeightOneSpectrum (𝓞 F)} (x g g' : UAd hc n)
    (hg : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (hg' : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) (g' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1)
    (h : decoOf ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoOf ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) :
    g⁻¹ * g' ∈ mhlKv hc n v := by
  have hr : decoRaw ST SG ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
      decoRaw ST SG ((x * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    rw [← rlc_decoOf_val hc n ST SG (x * g).2, ← rlc_decoOf_val hc n ST SG (x * g').2, h]
  have hK := mem_principal_of_same_decoration hc n ST SG (x * g).2 (x * g').2 hr
  have e : ((x * g : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ * ((x * g' : UAd hc n) : GL (Fin n) _) =
      ((g⁻¹ * g' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, _root_.mul_inv_rev]
    group
  rw [e] at hK
  refine mem_localLevel_of_mem_kOne ST SG (fun w hw => ?_) hK
  rw [Subgroup.coe_mul, InvMemClass.coe_inv, map_mul, map_inv, hg w hw, hg' w hw, inv_one, one_mul]

end Kv

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedUpDnA
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tud_locP_L {a : 𝓞 E} (ha : SepElt ST a) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) :
    localization₂ P.1.asIdeal d.1.L = localization₂ P.1.asIdeal (d.1.LshKer P) := by
  rw [d.2.locP_LshKer_self ha P]
  have key : ∀ (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ localization₂ P.1.asIdeal L ↔ ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ L := fun _ _ => Iff.rfl
  ext x
  rw [d.2.mem_locP_L P x, key]
  constructor
  · rintro ⟨hx, hf⟩
    obtain ⟨s, hs, hsx⟩ := (key _ x).1 hx
    refine ⟨s, hs, (d.2.mem_kerAt P _).2 ⟨hsx, ?_⟩⟩
    rw [d.2.f_smul P s x hx, hf, mul_zero]
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨hN, hf⟩ := (d.2.mem_kerAt P _).1 hsx
    have hx : x ∈ d.1.at P.1 := (key _ x).2 ⟨s, hs, hN⟩
    refine ⟨hx, ?_⟩
    rw [d.2.f_smul P s x hx] at hf
    rcases mul_eq_zero.1 hf with h0 | h0
    · exact absurd (Ideal.Quotient.eq_zero_iff_mem.1 h0) hs
    · exact h0

end Lat

section Same

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tud_isOver_conj (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (hov : IsOver v P) : IsOver v (conjPrime₂ P) := by
  unfold IsOver at *
  rw [hov]
  change _ = Ideal.comap _ (Ideal.comap (cO E) P.asIdeal)
  rw [Ideal.comap_comap]
  congr 1
  apply RingHom.ext
  intro x
  symm
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E)
  rw [hc.fixed]
  refine ⟨(x : F), ?_⟩
  rfl

end Same

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXpT
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem xp_mulLat_L (hc : CMData F E) {n : ℕ} [NeZero n] {ST SG : Finset (Pl E)} {H : Subgroup (GLG (E := E) (n := n) (SG := SG))} (g : UF E n × H)
    (e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    Formalism.L2.Forms.mulLat (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) e.1.L = (g • e).1.L := by
  rw [rlc_smul_val, Deco.L_act]
  unfold Formalism.L2.Forms.mulLat gmap
  congr 1
  apply LinearMap.ext
  intro x
  show (((ratEquiv hc n).symm g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = g.1.1 x
  rw [← rlc_ratHom_apply hc n]
  have : ratHom hc n ((ratEquiv hc n).symm g.1) = g.1 := (ratEquiv hc n).apply_symm_apply g.1
  rw [this]

def padL (E : Type) [Field E] (n N : ℕ) : (Fin n → E) →ₗ[E] (Fin N → E) where
  toFun x j := if h : (j : ℕ) < n then x ⟨j, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : (j : ℕ) < n <;> simp [h]

theorem padL_apply (E : Type) [Field E] (n N : ℕ) (x : Fin n → E) (j : Fin N) :
    padL E n N x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0 := rfl

theorem xp_tilH_L {N n : ℕ} (hN : N = n + 1) [NeZero N] {ST SG : Finset (Pl E)} (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (hpi : ∀ P : ST, pi ∈ P.1.asIdeal)
    (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r)
    (iX : (Fin n → E) →ₗ[E] (Fin N → E))
    (hiX : ∀ x (j : Fin N), iX x j = if h : (j : ℕ) < n then x ⟨j, h⟩ else 0) :
    (DecoSet.tilH (ST := ST) hN pi d).1.L = d.1.N.map (iX.restrictScalars (𝓞 E)) ⊔
      Submodule.span (𝓞 E) {(Pi.single (lastIdx N) (algebraMap (𝓞 E) E pi) : Fin N → E)} := by
  subst hN
  show (DecoSet.til (ST := ST) pi d).1.L = _
  rw [DecoSet.til_val d hT hG, d.2.til_L hT hG hpi hdvd]
  have e1 : iX = incl E n := by
    apply LinearMap.ext
    intro x
    funext j
    rw [hiX]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [incl]
    · simp [incl]
  have e2 : z0 E n (algebraMap (𝓞 E) E pi) = (Pi.single (lastIdx (n + 1)) (algebraMap (𝓞 E) E pi) : Fin (n + 1) → E) := by
    have hl : lastIdx (n + 1) = Fin.last n := Fin.ext (by simp [lastIdx])
    rw [hl]
    funext j
    simp [z0, eLast, Pi.single_apply]
  rw [e1, e2]

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem xp_crd_frame (i : ℕ) (hi : i ≤ d.R.m) (b : Fin (d.sp.X i).rank) :
    d.crd i hi ((d.sp.X i).frame b) = Pi.single (finCongr (d.sp.X_rank i hi) b) (1 : d.host.E) := by
  funext j
  show (d.sp.X i).frame.equivFun ((d.sp.X i).frame b) ((finCongr (d.sp.X_rank i hi)).symm j) = _
  simp only [Basis.equivFun_self, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

def ColDat.z0 (d : ColDat) (u : d.what₂.Word) : Fin (d.R.N d.R.m) → d.host.E :=
  Pi.single (lastIdx (d.R.N d.R.m)) (d.piT u : d.host.E)

theorem zc_eq (hS : SpStd d.toColBase) :
    ∃ c : d.host.E, c ≠ 0 ∧ CF.zc (d.colRec a) = Pi.single (lastIdx (d.R.N d.R.m)) c := by
  obtain ⟨c, hc⟩ := hS.z
  have hr := d.sp.X_rank d.R.m le_rfl
  set b₀ : Fin (d.sp.X d.R.m).rank := (finCongr hr).symm (lastIdx (d.R.N d.R.m)) with hb₀
  have hb : (b₀ : ℕ) + 1 = (d.sp.X d.R.m).rank := by
    have h1 : (b₀ : ℕ) = d.R.N d.R.m - 1 := rfl
    have := d.R.N_pos d.R.m
    omega
  have hz := hc b₀ hb
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    apply d.sp.z_anis
    rw [hz, zero_smul, map_zero]
  · show d.crd d.R.m le_rfl d.sp.z = _
    rw [hz, map_smul, xp_crd_frame, hb₀, Equiv.apply_symm_apply]
    funext j
    simp [Pi.single_apply]

theorem lastCoordinateUniformizerVector_spans_orthogonal_line (hS : SpStd d.toColBase) (u : d.what₂.Word) : ∃ c : d.host.E, d.z0 u = c • CF.zc (d.colRec a) := by
  obtain ⟨c, hc0, hc⟩ := zc_eq a hS
  refine ⟨(d.piT u : d.host.E) / c, ?_⟩
  rw [hc]
  funext j
  unfold ColDat.z0
  by_cases h : j = lastIdx (d.R.N d.R.m)
  · subst h
    simp [div_mul_cancel₀ _ hc0]
  · simp [h]

theorem hermitianForm_lastCoordinateUniformizerVector_self (hS : SpStd d.toColBase) (u : d.what₂.Word) :
    hform (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) (d.z0 u) (d.z0 u) =
      (((d.colRec a).mem u).A.T : d.host.E) := by
  rw [gramN_eq a hS]
  have h1 := rf_hform_one (X := d.X) (d.z0 u) (d.z0 u)
  refine Eq.trans h1 ?_
  rw [hStd_apply, Finset.sum_eq_single (lastIdx (d.R.N d.R.m))]
  · unfold ColDat.z0
    rw [Pi.single_eq_same]
    have h2 := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h2
    rw [mul_comm]
    exact h2
  · intro j _ hj
    unfold ColDat.z0
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

def ColDat.tilPt (d : ColDat) (u : d.what₂.Word) (c : PCl d) : DecoSet (E := d.X.E) (n := d.R.N d.R.m) (ST := d.Pr.vT u) (SG := d.Pr.vGs) :=
  tilR (Pr := d.Pr) (R := d.R) (Finset.Subset.refl _) u (d.reprP c)

def ColDat.tilMv (d : ColDat) (u : d.what₂.Word) (c : PCl d) : (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).G :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv (d.tilPt u c)

theorem tilMv_smul (u : d.what₂.Word) (c : PCl d) :
    d.tilMv u c • d.repr u d.R.m (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c) = d.tilPt u c :=
  (stepGSD (Pr := d.Pr) d.W d.lev u d.R.m).outSec.mv_smul (d.tilPt u c)

def ColDat.tilGa (d : ColDat) (u : d.what₂.Word) (c : PCl d) : URat d.sp.cm (d.R.N d.R.m) :=
  (ratEquiv d.sp.cm (d.R.N d.R.m)).symm (d.tilMv u c).1

def tieGa (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    UJ (CF.sigD (d.colRec a) : d.host.E →+* d.host.E) (CF.gramN (d.colRec a) d.R.m le_rfl) :=
  ⟨(d.tilGa u c).1, by rw [gramN_eq a hS]; exact (d.tilGa u c).2⟩

theorem coordinates_frame_eq_single (b : Fin d.sp.X'.rank) :
    CF.crdP (d.colRec a) (d.sp.X'.frame b) = Pi.single (finCongr (CF.rankP (d.colRec a)) b) (1 : d.host.E) := by
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame b) ((finCongr (CF.rankP (d.colRec a))).symm j) = _
  simp only [Basis.equivFun_self, Pi.single_apply, Equiv.eq_symm_apply, eq_comm]

theorem iXc_eq (hS : SpStd d.toColBase) : CF.iXc (d.colRec a) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) := by
  apply (Pi.basisFun d.host.E (Fin (d.R.N d.R.m - 1))).ext
  intro k
  rw [Pi.basisFun_apply]
  have hk : (k : ℕ) < d.R.N d.R.m := lt_of_lt_of_le k.2 (Nat.sub_le _ _)
  have h1 : (CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)) =
      d.sp.X'.frame ((finCongr (CF.rankP (d.colRec a))).symm k) := by
    rw [LinearEquiv.symm_apply_eq, coordinates_frame_eq_single, Equiv.apply_symm_apply]
  show d.crd d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (Pi.single k (1 : d.host.E)))) = _
  rw [h1, hS.iX' _ ((finCongr (d.sp.X_rank d.R.m le_rfl)).symm ⟨k, hk⟩) rfl, xp_crd_frame, Equiv.apply_symm_apply]
  funext j
  rw [padL_apply, Pi.single_apply]
  by_cases h : (j : ℕ) < d.R.N d.R.m - 1
  · rw [dite_eq_left h, Pi.single_apply]
    congr 1
    exact propext ⟨fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m) => (z : ℕ)) e),
      fun e => Fin.ext (show (j : ℕ) = k from congrArg (fun z : Fin (d.R.N d.R.m - 1) => (z : ℕ)) e)⟩
  · rw [dite_eq_right h, if_neg]
    rintro rfl
    exact h k.2

theorem til_lat (hS : SpStd d.toColBase) (u : d.what₂.Word) (c : PCl d) :
    Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1 (CF.clsCrd (d.colRec a) u d.R.m le_rfl
              (tilCl (Pr := d.Pr) d.W d.lev (Finset.Subset.refl _) d.levP u c)) =
      ((d.reprP c).1.N).map ((CF.iXc (d.colRec a)).restrictScalars (𝓞 d.host.E)) ⊔ Submodule.span (𝓞 d.host.E) {d.z0 u} := by
  rw [iXc_eq a hS]
  refine (congrArg (Formalism.L2.Forms.mulLat (tieGa a hS u c).1.1) (clsCrd_eq a u d.R.m le_rfl _)).trans ?_
  refine (xp_mulLat_L d.sp.cm (d.tilMv u c) _).trans ?_
  have h := tilMv_smul u c
  refine (congrArg (fun e : DecoSet (E := d.X.E) (n := d.R.N d.R.m) (ST := d.Pr.vT u) (SG := d.Pr.vGs) => e.1.L) h).trans ?_
  exact xp_tilH_L (N_m_succ d.R) (d.reprP c) (fun P => conj_piT_notMem d.hPr u P) (a.piT_off u)
    (fun P => decoFin_mem_of_mem_divs P.2) (fun r hr => piT_dvd_of_mem d.hX d.hPr u r hr) _ (padL_apply _ _ _)

end Rec

end Formalism.L2.Col
end
end

