module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0429

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryDetCharacterEqProdResidueGoodBaseFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStabAll

open Classical GlobalTheory.TwistDetStab

variable {D : D7}

theorem exists_finUnit_isDetRoot {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {k : GA D V} (hk : k ∈ GfC V)
    (hst : Lev.finE V k ∈ St β) : ∃ x : (AE D)ˣ, Formalism.L2.Pj.FinUnit x ∧ IsDetRoot V k x := by
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  obtain ⟨a, ha, -⟩ := GlobalTheory.VecInv.exists_det_int hst
  have hd : finPart D (mt V k).det ∈ intAE D := GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (ha ▸ a.2)
  have hw : (finHom V k).1.det - 1 ∈ intAE D :=
    sub_mem (hdet ▸ hd) (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (_root_.mul_one _))
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, -⟩ := GlobalTheory.OddRoot.exists_root_odd D 1 odd_one _ _ hw (one_nsmul _).symm hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_⟩
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', GlobalTheory.UnitDetRoot.infPart_sigR_one D _ hY1, hY1, _root_.mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

theorem chi_detAt {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    {β : GL (Fin V.rank) (Lev.EAf D)} {κ : GA D V} (hst : Lev.finE V κ ∈ St β) (he : idem t.Q * idem t.Q = idem t.Q) :
    t.chi (GlobalTheory.VecInv.detAt (idem t.Q) he V κ) =
      ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (ht.split.isIdemAt hP).1.1
  have hsplit : GlobalTheory.VecInv.detAt (idem t.Q) he V κ =
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.coe_prod]
    show idem t.Q * (mt V κ).det + (1 - idem t.Q) = ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _)]
  rw [hsplit, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (ht.split.isIdemAt P.2)).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

def offUnit {R : Type} [CommRing R] (f : R) (hf : f * f = f) (x : Rˣ) : Rˣ where
  val := f + (1 - f) * x.val
  inv := f + (1 - f) * (x⁻¹).val
  val_inv := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf
  inv_val := by
    linear_combination (1 - f) ^ 2 * x.mul_inv + (2 - x.val - (x⁻¹).val) * hf

theorem cmRing_idempotent_unitRatio_identity {R : Type} [CommRing R] (c : R →+* R) (hc : ∀ z, c (c z) = z) (e d x : R) (h1 : e * e = e)
    (h2 : e * c e = 0) (hd : c d * d = 1) (hx : x = d * c x) :
    (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) =
      d * c ((e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have k : (e * d + (1 - e)) * ((e + c e) + (1 - (e + c e)) * x) = e * d + c e + (1 - (e + c e)) * x := by
    linear_combination (d - 1) * (1 - x) * (h1 + h2)
  rw [k]
  simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
  linear_combination (1 - (e + c e)) * hx - c e * hd

theorem finPart_off_mem (f y : AE D) (hf : f * f = f) (hy : finPart D y ∈ intAE D) :
    finPart D (f + (1 - f) * y) ∈ intAE D := by
  have h1 : finPart D f ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hf])
  have h2 : finPart D (1 - f) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by
    rw [← RingHom.map_mul]; congr 1; linear_combination hf)
  rw [RingHom.map_add (f := _), RingHom.map_mul]
  exact add_mem h1 (GlobalTheory.HeckeConj.mul_mem_intAE D h2 hy)

theorem detChar_eq_prod_res_of_frame {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A) (ht : t.Good)
    (β : GL (Fin V.rank) (Lev.EAf D)) {κ : GA D V} (hκ : κ ∈ GfC V) (hst : Lev.finE V κ ∈ St β) :
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx⟩ := exists_finUnit_isDetRoot hκ hst
  have he : idem t.Q * idem t.Q = idem t.Q := idem_mul_self ht.split
  have hce : idem t.Q * cA D (idem t.Q) = 0 := ht.split.isIdemSum.2
  have hcc : cA D (idem t.Q) * cA D (idem t.Q) = cA D (idem t.Q) := by rw [← RingHom.map_mul, he]
  have hf : (idem t.Q + cA D (idem t.Q)) * (idem t.Q + cA D (idem t.Q)) = idem t.Q + cA D (idem t.Q) := by
    linear_combination he + hcc + 2 * hce
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem t.Q) he V κ * offUnit _ hf x) :=
    cmRing_idempotent_unitRatio_identity (cA D) GlobalTheory.DualPairCheck.cA_cA (idem t.Q) (mt V κ).det x he hce (det_conj_mul V κ) hx
  have hw : t.chi (offUnit _ hf x) = 1 := by
    refine ht.unram _ ?_ (finPart_off_mem _ _ hf hx2) (finPart_off_mem _ _ hf hx3) ?_
    · show infPart D (_ + (1 - _) * (x : AE D)) = 1
      rw [RingHom.map_add (f := _), RingHom.map_mul, hx1, RingHom.map_sub, RingHom.map_one]
      ring
    · show (idem t.Q + cA D (idem t.Q)) * ((idem t.Q + cA D (idem t.Q)) + (1 - (idem t.Q + cA D (idem t.Q))) * (x : AE D)) = _
      linear_combination (1 - (x : AE D)) * hf
  rw [detChar_eq ht.real hroot, map_mul, hw, _root_.mul_one, chi_detAt t ht hst he]

theorem detChar_eq_prod_res : ∀ {D : D7} {S T : HSp D} (B : Base S T), B.Good → ∀ {A : Type} [CommGroup A] (t : Twist D A),
    t.Good → ∀ {κ : GA D T}, κ ∈ GfC T → Lev.finE T κ ∈ St B.F.βT →
    detChar T t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn B.F.βT PP (Lev.finE T κ))) :=
  fun B _ _ _ t ht _ hκ hst => detChar_eq_prod_res_of_frame t ht B.F.βT hκ hst

end GlobalTheory.TwistDetStabAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCharSpreadCommutesWithRestriction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SpreadRestrict

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X}

theorem surj_conj {B : Type} [CommGroup B] (χ : G D.host.E N.Om →* B) (hA : AntiHom X.cc χ)
    {P P' : PlE D.host} (hPP : IsConjPl D.host P P')
    (hs : ∀ A : ValuationSubring N.Om, IsPlaceOver A P → ∀ b : B, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b)
    (A : ValuationSubring N.Om) (hA' : IsPlaceOver A P') (b : B) : ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    Formalism.BasicNotions.bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := X.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, X.cc (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E N.Om)) x).symm
  have hs' : ∀ x, X.cc.symm (algebraMap D.host.E N.Om x) =
      algebraMap D.host.E N.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hinv : ∀ x, X.cc (X.cc x) = x := fun x => by
    apply j.injective
    rw [hj, hj]
    simp
  have hsymm : ∀ x, X.cc.symm x = X.cc x := fun x => by
    rw [RingEquiv.symm_apply_eq, hinv]
  have hP'P := GlobalTheory.GalChar.isConjPl_symm hPP
  have hpl : IsPlaceOver (A.comap X.cc.symm.toRingHom) P := fun y => by
    have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [GlobalTheory.AntiRam.valuation_comap_lt_one, hs', ← hP'P ⟨_, hint⟩ y (hκ _).symm]
    exact hA' ⟨_, hint⟩
  obtain ⟨σ, hσ, hσb⟩ := hs _ hpl b⁻¹
  obtain ⟨σ', h1, h2⟩ := GlobalTheory.AntiRam.exists_conj_mem_Ine X.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  have eA : (A.comap X.cc.symm.toRingHom).comap X.cc.symm.toRingHom = A := by
    ext y
    show X.cc.symm (X.cc.symm y) ∈ A ↔ y ∈ A
    rw [hsymm, hsymm, hinv]
  refine ⟨σ', eA ▸ h2, ?_⟩
  rw [hA σ σ' h1, hσb, inv_inv]

theorem sign_eq_one (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {S : Finset (Pl D.host.E)} {M : ℕ}
    {P v : Pl D.host.E} (hP : P ∈ S) (hv : v ∈ S) (hc : IsConjPl D.host P v) (hPa : P ∈ admissibleConjugatePairPlaces X i S M) :
    (((Y.delU_conj i S M P hP v hv hc).choose : ℤ) : ZMod (X.l i ^ M)) = 1 := by
  classical
  have hs := (Y.delU_conj i S M P hP v hv hc).choose_spec
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := conj_mem_admissibleConjugatePairPlaces hPa hc
  obtain ⟨-, P', -, -, hadm⟩ := mem_admissibleConjugatePairPlaces_iff.1 hPa
  obtain ⟨-, χ, h1, h2, h3, h4, h5⟩ := hadm.2 P (by simp)
  have hDel : GlobalTheory.GalChar.IsDel D.host X.cc (X.l i) M (GlobalTheory.GalChar.pair D.host P) χ := by
    refine ⟨h1, h2, h3, fun w hw => h4 w (fun e => hw (Or.inl e)) (fun e => hw (Or.inr e)), fun w hw A hA b => ?_⟩
    have hsP : ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        ∀ b, ∃ σ ∈ Ine (F := D.host.E) A, χ σ = b := fun A hA b => by
      obtain ⟨σ, hσ⟩ := h5 A hA (Multiplicative.toAdd b)
      exact ⟨σ.1, σ.2, Multiplicative.toAdd.injective hσ⟩
    rcases hw with rfl | hw
    · exact hsP A hA b
    · exact surj_conj χ h2 hw hsP A hA b
  have hD := GlobalTheory.GalChar.isDel_delOf D.host X.cc (X.l i) ⟨χ, hDel⟩
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P
  obtain ⟨σ, -, hσ⟩ := hD.2.2.2.2 P (Or.inl rfl) A hA (Multiplicative.ofAdd 1)
  have e := hs σ
  rw [delU_on hY σ ⟨v, hv⟩ hva, delU_on hY σ ⟨P, hP⟩ hPa] at e
  simp only at e
  rw [GlobalTheory.GalChar.pair_eq hc, hσ, toAdd_ofAdd, mul_one] at e
  exact e.symm

theorem spread_conj (hY : GlobalTheory.UnivChar.IsUnivChar Y) {i : X.Tw} {M : ℕ} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    {S : Finset (Pl D.host.E)} (hS : admissibleConjugatePairPlaces X i S M = S) (x : ↥(half ch (admissibleConjugatePairPlaces X i S M)) → ZMod (X.l i ^ M))
    {v P : Pl D.host.E} (hvS : v ∈ S) (hvc : v ∉ ch) (hvP : IsConjPl D.host v P)
    (hPh : P ∈ half ch (admissibleConjugatePairPlaces X i S M)) :
    spread Y i S M ch x ⟨v, hvS⟩ = x ⟨P, hPh⟩ := by
  have hva : v ∈ admissibleConjugatePairPlaces X i S M := by rw [hS]; exact hvS
  have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
  have hPv := GlobalTheory.GalChar.isConjPl_symm hvP
  have hPaa : P ∈ admissibleConjugatePairPlaces X i (admissibleConjugatePairPlaces X i S M) M := by
    simp only [hS]
    rw [← hS]
    exact (mem_half.1 hPh).1
  rw [spread_apply, Finset.sum_eq_single ⟨P, hPh⟩, weight, if_neg hne, dite_eq_left ⟨hva, hPv⟩, sign_eq_one hY _ _ hPv hPaa,
    one_mul]
  · intro P' _ h'
    rw [weight, if_neg fun e : v = P'.1 => hvc (e ▸ (mem_half.1 P'.2).2), dite_eq_right fun h => h' (Subtype.ext
      (GlobalTheory.GalChar.isConjPl_unique (GlobalTheory.GalChar.isConjPl_symm h.2) hvP)), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem spread_restrict : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (M : ℕ) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (Q Q' : Finset (Pl D.host.E)) (hQQ : Q' ⊆ Q), admissibleConjugatePairPlaces X i Q M = Q → admissibleConjugatePairPlaces X i Q' M = Q' → ∀ (hsub : ∀ w ∈ half ch (admissibleConjugatePairPlaces X i Q' M), w ∈ half ch (admissibleConjugatePairPlaces X i Q M)) (c : ↥(half ch (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) (v : Pl D.host.E) (hv : v ∈ Q'), spread Y i Q M ch c ⟨v, hQQ hv⟩ = spread Y i Q' M ch (fun w => c ⟨w.1, hsub w.1 w.2⟩) ⟨v, hv⟩ := by
  intro D N X Y hY i M ch hch Q Q' hQQ hQ hQ' hsub c v hv
  by_cases hc : v ∈ ch
  · have h1 : v ∈ half ch (admissibleConjugatePairPlaces X i Q M) := mem_half.2 ⟨by rw [hQ]; exact hQQ hv, hc⟩
    have h2 : v ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨by rw [hQ']; exact hv, hc⟩
    rw [spread_of_mem Y i Q M hch c ⟨v, hQQ hv⟩ h1, spread_of_mem Y i Q' M hch _ ⟨v, hv⟩ h2]
  · have hva : v ∈ admissibleConjugatePairPlaces X i Q' M := by rw [hQ']; exact hv
    obtain ⟨-, P, -, hvP, -⟩ := mem_admissibleConjugatePairPlaces_iff.1 hva
    have hne : v ≠ P := ne_of_split (isSplit_of_mem_admissibleConjugatePairPlaces hva) hvP
    have hPc : P ∈ ch := by
      by_contra h
      exact hc ((hch.pair _ _ hvP hne).2 h)
    have hPa' : P ∈ admissibleConjugatePairPlaces X i Q' M := conj_mem_admissibleConjugatePairPlaces hva hvP
    have hPh' : P ∈ half ch (admissibleConjugatePairPlaces X i Q' M) := mem_half.2 ⟨hPa', hPc⟩
    rw [spread_conj hY hch hQ c (hQQ hv) hc hvP (hsub P hPh'), spread_conj hY hch hQ' _ hv hc hvP hPh']

end GlobalTheory.SpreadRestrict

end
end

