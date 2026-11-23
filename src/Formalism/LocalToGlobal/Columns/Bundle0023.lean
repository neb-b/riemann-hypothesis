module

public import Formalism.LocalToGlobal.Columns.Bundle0021
public import Formalism.LocalToGlobal.Columns.AtTOwedS
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.TiedCG
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Formalism.LocalToGlobal.Columns.TwQDefs

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.TiedAtT
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

include hPr in
theorem att_T_mem_under (P : {P // P ∈ Pr.vT u}) : (Pr.T u : 𝓞 X.F) ∈ (underPl X.F P.1).asIdeal := by
  show (Pr.T u : 𝓞 X.F) ∈ P.1.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E))
  rw [Ideal.mem_comap, map_natCast]
  exact T_mem hPr u P

def tieEV : {P // P ∈ Pr.vT u} ≃ {v : HeightOneSpectrum (𝓞 X.F) // (Pr.T u : 𝓞 X.F) ∈ v.asIdeal} :=
  Equiv.ofBijective (fun P => ⟨underPl X.F P.1, att_T_mem_under hPr u P⟩) (by
    constructor
    · intro P Q h
      have h1 : underPl X.F P.1 = underPl X.F Q.1 := congrArg Subtype.val h
      have hP : IsOver (underPl X.F P.1) P.1 := rfl
      have hQ : IsOver (underPl X.F P.1) Q.1 := by rw [h1]; rfl
      exact Subtype.ext ((basePi_of_ok hX hPr u).over_unique hc P.2 hP Q.1 Q.2 hQ).symm
    · rintro ⟨v, hv⟩
      obtain ⟨P, hP, hov⟩ := (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).2 hv
      exact ⟨⟨P, hP⟩, Subtype.ext (HeightOneSpectrum.ext hov.symm)⟩)

end Gen

section Val

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 K))
  (hval : ∀ w (x : K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))


include hval in
theorem att_val_pos (w : Pl.Pl) (x : 𝓞 K) : (0 : WithTop ℤ) < Pl.val w (x : K) ↔ x ∈ (pw w).asIdeal := by
  by_cases hx : x = 0
  · subst hx
    have h0 : Pl.val w (((0 : 𝓞 K) : 𝓞 K) : K) = ⊤ := by
      rw [show (((0 : 𝓞 K) : 𝓞 K) : K) = 0 from rfl]
      exact (Pl.val w).map_zero
    rw [h0]
    exact ⟨fun _ => zero_mem _, fun _ => WithTop.coe_lt_top (0 : ℤ)⟩
  · have hx' : (x : K) ≠ 0 := fun h => hx (RingOfIntegers.ext h)
    have h0 : (pw w).valuation K (x : K) ≠ 0 := (Valuation.ne_zero_iff _).2 hx'
    rw [hval w _ hx', ← (pw w).valuation_lt_one_iff_mem (K := K)]
    unfold Formalism.BasicNotions.vAdd
    rw [← WithTop.coe_zero, WithTop.coe_lt_coe, neg_pos, ← WithZero.log_one, WithZero.log_lt_log h0 one_ne_zero]


include hval in
theorem att_resChar_mem (w : Pl.Pl) : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ (pw w).asIdeal := by
  rw [← att_val_pos Pl pw hval]
  have h := Pl.val_resChar w
  have e : ((((Pl.resChar w : ℕ) : 𝓞 K) : 𝓞 K) : K) = ((Pl.resChar w : ℕ) : K) := map_natCast (algebraMap (𝓞 K) K) _
  rw [e, h, ← WithTop.coe_zero, WithTop.coe_lt_coe]
  exact_mod_cast Pl.ramIdx_pos w

end Val

section Seen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)


include hc in
theorem att_mem_conjP (P : Pl X.E) (x : 𝓞 X.F) :
    algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime₂ P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal := by
  rw [mem_conjP, rll_cO_algebraMap hc]

theorem att_tauOf (w : HeightOneSpectrum (𝓞 X.K)) (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) (x : 𝓞 X.F) :
    x ∈ (tieEV hc hX hPr u P).1.asIdeal ↔ X.embO (tauOfR hX hPr u w P) (algebraMap (𝓞 X.F) (𝓞 X.E) x) ∈ w.asIdeal := by
  have := hX.nonempty_Tau
  have e : tauOfR hX hPr u w P = tauOfC w P.1 := by
    unfold tauOfR
    rw [dite_eq_left hw]
    rfl
  rw [e, ← mem_pullW]
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.1.asIdeal ↔ _
  rcases tauOfC_spec hX hPr u w hw P with h | h
  · rw [show pullW (tauOfC w P.1) w = P.1 from h]
  · rw [show pullW (tauOfC w P.1) w = conjPrime₂ P.1 from h, att_mem_conjP hc]


end Seen

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem att_star_eq (x : d.host.E) : star x = d.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj d.host x


set_option maxHeartbeats 1000000 in
def atTTied (hH : HostHyp d) (u : d.what₂.Word) : CF.AtTTied (D := d.colRec a) u where
  eV := tieEV d.sp.cm d.hX d.hPr u
  piU := d.piT u
  piU_K := hH.piT_K u
  piU_norm := by
    have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piT_norm u)
    rw [map_mul, map_natCast] at h
    rw [← att_star_eq]
    exact h
  piU_cong := by
    rw [Ideal.mem_span_singleton]
    have h := d.hPr.piT_cong u
    have e : d.Pr.cond = d.host.QS * d.host.q * d.host.d := hH.cond_eq
    rw [e] at h
    exact h
  res := fun v => Ideal.Quotient.mk v.1.asIdeal
  res_surj := fun v => Ideal.Quotient.mk_surjective
  res_pi := fun v => Ideal.Quotient.eq_zero_iff_mem.2 ((rls_vT_iff d.hX d.hPr u v.1).1 v.2)
  res_conj := fun v pb hpb h => by
    have h1 : pb = cO d.X.E (d.Pr.piT u) := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 d.X.E) d.X.E pb = algebraMap (𝓞 d.X.E) d.X.E (cO d.X.E (d.Pr.piT u))
      rw [algebraMap_cO, att_star_eq (d := d)]
      exact hpb
    change Ideal.Quotient.mk v.1.asIdeal pb = 0 at h
    rw [h1] at h
    exact (basePi_of_ok d.hX d.hPr u).conj_notMem v.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  res_v := fun v x => (Ideal.Quotient.eq_zero_iff_mem (I := v.1.asIdeal)).symm
  tauOf := fun w hw v x => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    exact (att_tauOf d.sp.cm d.hX d.hPr u (d.plEq w) hT v x).trans (att_val_pos d.what₂.places d.plEq hH.val_eq w _).symm
  seenP := fun w hw τ => by
    have hT : (d.Pr.T u : 𝓞 d.X.K) ∈ (d.plEq w).asIdeal := by
      have := att_resChar_mem d.what₂.places d.plEq hH.val_eq w
      rw [hw] at this
      exact this
    have key : ∀ b : Bool, b = (open Classical in decide (seenC d.Pr u (d.plEq w))) →
        (0 : WithTop ℤ) < d.what₂.places.val w (d.embE (d.host.sigmaOf (d.eTau τ : d.R.GG)
          (if b = true then (d.piT u : d.host.E) else d.host.conj (d.piT u : d.host.E)))) := by
      intro b hb
      by_cases hs : seenC d.Pr u (d.plEq w)
      · have hb' : b = true := by rw [hb]; exact @decide_eq_true _ (Classical.propDecidable _) hs
        rw [if_pos hb']
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.Pr.piT u))).2 (hs τ)
      · have hb' : ¬ b = true := by rw [hb]; simpa using hs
        rw [if_neg hb', ← att_star_eq]
        exact (att_val_pos d.what₂.places d.plEq hH.val_eq w (d.X.embO τ (d.X.conjO (d.Pr.piT u)))).2
          (((seenC_or_seenBarC d.hX d.hPr u (d.plEq w) hT).resolve_left hs) τ)
    exact key _ rfl

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedXp
section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_basePi_one : BasePi (∅ : Finset (Pl X.E)) (1 : 𝓞 X.E) :=
  ⟨fun r => ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩,
    isCoprime_one_left⟩

theorem xp_L_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (Pl E)}
    (d : Deco E n (∅ : Finset (Pl E)) SG) : d.L = d.N := by
  unfold Deco.L
  have : {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (Pl E)), d.f P x = 0} = (d.N : Set (Sp E n)) := by
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty P.1)⟩
  rw [this, Submodule.span_eq]

def tieLevP : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := ∅) (SG := Pr.vGs))

def clsPG₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  lev := tieLevP hc σ₀ Λ
  y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
  y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
  y_lat := fun c x => by
    have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
    rw [xp_L_eq_N] at h
    exact h
  stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
  stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range c γ.1 γ.2

def clsPG (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    ClsG hc.sig Q.J 1 Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsPG₁ hc σ₀ Λ s hS hs

end GenP

section Rec

variable {d : ColDat}

abbrev PCl (d : ColDat) : Type := (ptGSD (Pr := d.Pr) d.W d.levP).Cl

def ColDat.reprP (d : ColDat) (c : PCl d) : DecoSet (E := d.X.E) (n := d.R.N d.R.m - 1) (ST := ∅) (SG := d.Pr.vGs) :=
  (ptGSD (Pr := d.Pr) d.W d.levP).outSec.rep c

def crdPr (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) :
    StepCrd d.Pr d.σ₀ (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  J := CF.gramP (d.colRec a)
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := fun c => (d.reprP c).1.N
  l0 := stdLat d.X.E (d.R.N d.R.m - 1)
  hJ := gramP_eq a hS
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := rfl
  hl0 := rfl

def PtSurjP (d : ColDat) : Prop := DecoPtSurj d.sp.cm (d.R.N d.R.m - 1) (∅ : Finset (Pl d.X.E)) d.Pr.vGs

def pClsG (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) :=
  clsPG d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH)

def parabolicClassAgreement (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)
    (hP : PtSurjP d) (u : d.what₂.Word) :
    CF.ClsPTied (D := d.colRec a) u where
  lev := (pClsG a hS hH hP).lev
  y := (pClsG a hS hH hP).y
  y_bij := (pClsG a hS hH hP).y_bij
  lat := fun c => (d.reprP c).1.N
  y_lat := (pClsG a hS hH hP).y_lat
  lat_fin := fun c => Module.Finite.iff_fg.2 (d.reprP c).2.lat.fg
  stabI := (pClsG a hS hH hP).stabI
  stabI_inj := (pClsG a hS hH hP).stabI_inj
  stabI_range := (pClsG a hS hH hP).stabI_range

end Rec

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TwQSplit
section
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)

theorem qsp_exists_pi (P : Pl E) (hP : conjPrime₂ P ≠ P) : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal := by
  obtain ⟨s, hs, hns⟩ := exists_mem_notMem (Ne.symm hP)
  exact ⟨s, hs, fun h => hns ((mem_conjP P s).2 h)⟩


include hc in
theorem qsp_norm_mem (a : 𝓞 E) : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = a * cO E a := by
  have h1 : star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a) := by
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm]
  obtain ⟨x, hx⟩ := (hc.fixed _).1 h1
  have hi : IsIntegral ℤ x := by
    have h2 : IsIntegral ℤ (algebraMap F E x) := by rw [hx]; exact RingOfIntegers.isIntegral_coe _
    exact (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) F b = x := ⟨⟨x, hi⟩, rfl⟩
  refine ⟨b, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) b) = algebraMap (𝓞 E) E (a * cO E a)
  rw [← hx, ← hb, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem qsp_isOver (P : Pl E) : IsOver (underPl F P) P := rfl


include hc in
theorem qsp_exists (P : Pl E) (hP : conjPrime₂ P ≠ P) :
    ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ cO E ϖ ∉ P.asIdeal ∧ Nonempty (Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E)) := by
  obtain ⟨ϖ, hϖ, hcϖ⟩ := qsp_exists_pi P hP
  obtain ⟨t, ht⟩ := gls_trace_mem hc ϖ
  obtain ⟨N, hN⟩ := qsp_norm_mem hc ϖ
  have hsig : ∀ x : E, hc.sig x = star x := fun _ => rfl
  have hsig0 : hc.sig (ϖ : E) = ((cO E ϖ : 𝓞 E) : E) := by rw [hsig]; exact (algebraMap_cO ϖ).symm
  have hN' : algebraMap F E (N : F) = (ϖ : E) * hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hN
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have ht' : algebraMap F E (t : F) = (ϖ : E) + hc.sig (ϖ : E) := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_add (f := _), ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
    rw [hsig0]; exact this
  have hNv : N ∈ (underPl F P).asIdeal := by
    show algebraMap (𝓞 F) (𝓞 E) N ∈ P.asIdeal
    rw [hN]; exact Ideal.mul_mem_right _ _ hϖ
  have htv : t ∉ (underPl F P).asIdeal := by
    intro h
    have h1 : algebraMap (𝓞 F) (𝓞 E) t ∈ P.asIdeal := h
    rw [ht] at h1
    exact hcϖ (by simpa using P.asIdeal.sub_mem h1 hϖ)
  obtain ⟨s⟩ := Formalism.MainNotions.Gaps.LG.sc_core hc.sig (fun x => by rw [hsig, hsig, star_star])
    (fun x hx => (hc.fixed x).1 hx) hc.deg2 (underPl F P) ϖ t N ht' hN' hNv htv
  have hN2 : ((cO E ϖ : 𝓞 E) : E) * hc.sig ((cO E ϖ : 𝓞 E) : E) = algebraMap F E (N : F) := by
    rw [hN', ← hsig0, mul_comm, hsig, hsig, star_star]
  obtain ⟨sa⟩ := Formalism.MainNotions.Gaps.LG.sc_orient s (cO E ϖ) N hNv hN2
  have e : hc.sig ((cO E ϖ : 𝓞 E) : E) = (ϖ : E) := by rw [← hsig0, hsig, hsig, star_star]
  exact ⟨ϖ, hϖ, hcϖ, ⟨e ▸ sa⟩⟩

end Split

end Formalism.L2.Col
end
end

