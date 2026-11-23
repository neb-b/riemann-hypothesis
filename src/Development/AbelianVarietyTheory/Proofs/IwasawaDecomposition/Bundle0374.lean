module

public import Mathlib
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Formalism.LocalToGlobal.Columns.RecLevelCls
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCardCodeWordStagesFiniteGroupEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.Mem.CyclotomicFieldContainment

theorem natCard_codeWordStages_finiteGroup_eq (X : Stages) : Nat.card (G0g X.toD7.nd) = X.B.restRowsFiniteGroupCard := by
  have : ∀ k, NeZero (X.toD7.host.g k) := fun k => ⟨(X.toD7.host.g_prime k).ne_zero⟩
  rw [Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change ∏ _y : X.toD7.nd.PlG k, Nat.card (GL (Fin X.toD7.R.r) (ZMod (X.toD7.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, X.toD7.nd.card_PlG k]
  rfl

theorem rootsField_le_iff (X : Stages) {N : IntermediateField ℚ ℂ} :
    rootsField X.B.toPre ≤ N ↔ ∀ n ∈ rootOrders X.toD7, cycField n ≤ N := by
  simp only [rootsField, rootOrders, natCard_codeWordStages_finiteGroup_eq, sup_le_iff, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_assoc]
  rfl

theorem rootOrders_ne_zero (X : Stages) : ∀ n ∈ rootOrders X.toD7, n ≠ 0 := by
  have hg : ∀ k, X.toD7.host.g k * (X.toD7.host.g k - 1) ≠ 0 := fun k => by
    have hp := X.toD7.host.g_prime k
    exact mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  simp only [rootOrders, natCard_codeWordStages_finiteGroup_eq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨X.B.restRowsFiniteGroupCard_pos.ne', hg 0, hg 1, by norm_num, by norm_num⟩

variable (ι : Qb →+* ℂ)

theorem le_map_of_qb_le {A : IntermediateField ℚ ℂ} {Y : Fld} (hA : ∀ z ∈ A, ∃ x, ι x = z) (h : qb ι A ≤ Y) :
    A ≤ Y.map ι.toRatAlgHom := fun z hz => by
  obtain ⟨x, rfl⟩ := hA z hz
  exact ⟨x, h (mem_qb.2 hz), rfl⟩

theorem muFld_le_qb {n : ℕ} (hn : n ≠ 0) {N : IntermediateField ℚ ℂ} (h : cycField n ≤ N) : muFld n ≤ qb ι N := by
  rw [muFld, IntermediateField.adjoin_le_iff]
  intro x hx
  refine mem_qb.2 (h (mem_cycField hn ?_))
  rw [← map_pow, show x ^ n = 1 from hx, map_one]

theorem cycField_le_map {n : ℕ} (hn : n ≠ 0) {Y : Fld} (hY : muFld n ≤ Y) (hz : ∃ x, ι x = rootOne n) :
    cycField n ≤ Y.map ι.toRatAlgHom := by
  obtain ⟨x, hx⟩ := hz
  refine cycField_le_iff.2 ⟨x, hY (IntermediateField.subset_adjoin ℚ _ ?_), hx⟩
  apply ι.injective
  rw [map_pow, hx, map_one]
  exact (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

variable {E : Type} [Field E] [NumberField E]

theorem valsOf_subset_qb {χ : Formalism.L2.Host.HChar E} {s : ℝ} {N : IntermediateField ℚ ℂ} (h : valueField χ s ≤ N) :
    valsOf ι s χ ⊆ qb ι N := fun _ ⟨v, hv, e⟩ =>
  mem_qb.2 (h (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, e⟩))

theorem valueField_le_map {χ : Formalism.L2.Host.HChar E} {s : ℝ} {Y : Fld} (hY : valsOf ι s χ ⊆ Y)
    (hz : ∀ z ∈ valueField χ s, ∃ x, ι x = z) : valueField χ s ≤ Y.map ι.toRatAlgHom := by
  rw [valueField, IntermediateField.adjoin_le_iff]
  rintro z ⟨v, hv, rfl⟩
  obtain ⟨x, hx⟩ := hz _ (IntermediateField.subset_adjoin ℚ _ ⟨v, hv, rfl⟩)
  exact ⟨x, hY ⟨v, hv, hx⟩, hx⟩

theorem ksQ_eq (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (hx : X.B.KsExact δ f) (T : HostTied X.toD7)
    (P : KsPieces X.toD7 T) (hR : P.rcf = qb T.fr.ι δ.ray) (hM : P.M = qb T.fr.ι δ.M) (hD : P.MDel = qb T.fr.ι δ.M')
    (hK : P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j)) :
    KsQ X.toD7 T (Fr.at X f) P = qb T.fr.ι (listField δ f) := by
  have hran : ∀ z ∈ listField δ f, ∃ x, T.fr.ι x = z := by
    intro z hz
    have hz' : z ∈ X.B.KsC := by rw [show X.B.KsC = listField δ f from hx]; exact hz
    obtain ⟨x, -, rfl⟩ := hz'
    exact ⟨T.jLL x, T.embLL x⟩
  have hle : ∀ {A : IntermediateField ℚ ℂ}, A ≤ listField δ f → ∀ z ∈ A, ∃ x, T.fr.ι x = z :=
    fun h z hz => hran z (h hz)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (listField_le_iff δ f).1 le_rfl
  have hKP : (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) ≤ listField δ f :=
    iSup₂_le fun j hj => h6 j hj.1 hj.2
  have hroots := (rootsField_le_iff X).1 h4
  have hne := rootOrders_ne_zero X
  simp only [charField, sup_le_iff, iSup_le_iff] at h5
  obtain ⟨⟨⟨⟨hmu, heta⟩, hdel⟩, hdel'⟩, hom⟩ := h5
  apply le_antisymm
  · have hM' : P.M ≤ qb T.fr.ι (listField δ f) := by
      rw [hM]
      exact fun x hx => mem_qb.2 (h2 (δ.M_le_M' hx))
    simp only [KsQ, sup_le_iff, iSup_le_iff]
    refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hM'⟩, ?_⟩, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact mem_qb.2 (h1 ⟨a, (T.fr.phi0 a).symm⟩)
    · exact fun n hn => muFld_le_qb _ (hne n hn) (hroots n hn)
    · rw [valsFld, IntermediateField.adjoin_le_iff]
      rintro x (((hx | hx) | hx) | hx)
      · obtain ⟨j, hx⟩ := Set.mem_iUnion.1 hx
        exact valsOf_subset_qb _ (hmu j) hx
      · exact valsOf_subset_qb _ heta hx
      · exact valsOf_subset_qb _ hdel hx
      · exact valsOf_subset_qb _ hdel' hx
    · rw [hR]; exact fun x hx => mem_qb.2 (h3 hx)
    · rw [hD]; exact fun x hx => mem_qb.2 (h2 hx)
    · rw [hK]; exact fun x hx => mem_qb.2 (hKP hx)
  · obtain ⟨Y, hYe⟩ : ∃ Y, Y = KsQ X.toD7 T (Fr.at X f) P := ⟨_, rfl⟩
    have hY : KsQ X.toD7 T (Fr.at X f) P ≤ Y := hYe.ge
    rw [← hYe]
    simp only [KsQ, sup_le_iff, iSup_le_iff] at hY
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩, a7⟩ := hY
    have ha3 : ∀ {A : Set Qb}, A ⊆ valsFld X.toD7 T (Fr.at X f) → A ⊆ Y := fun h _ hx => a3 (h hx)
    have hv : (⋃ j, valsOf T.fr.ι 0 ((Fr.at X f).mu0 j)) ∪ valsOf T.fr.ι (1 / 2) (Fr.at X f).eta ∪
        valsOf T.fr.ι 0 (Fr.at X f).del ∪ valsOf T.fr.ι 0 (Fr.at X f).del' ⊆ Y :=
      ha3 (IntermediateField.subset_adjoin ℚ _)
    have hr : rootsField X.B.toPre ≤ Y.map T.fr.ι.toRatAlgHom := (rootsField_le_iff X).2 fun n hn =>
      cycField_le_map _ (hne n hn) (a2 n hn) (hran _ (hroots n hn (IntermediateField.mem_adjoin_simple_self ℚ _)))
    have hmap : listField δ f ≤ Y.map T.fr.ι.toRatAlgHom := by
      refine (listField_le_iff δ f).2 ⟨?_, ?_, ?_, hr, ?_, fun j hj hj' => ?_⟩
      · rintro _ ⟨a, rfl⟩
        exact ⟨T.fr.j a, a1 ⟨a, rfl⟩, T.fr.phi0 a⟩
      · exact le_map_of_qb_le _ (hle h2) (hD ▸ a6)
      · exact le_map_of_qb_le _ (hle h3) (hR ▸ a4)
      · simp only [charField, sup_le_iff, iSup_le_iff]
        refine ⟨⟨⟨⟨fun j => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, hx⟩))))) (hle (hmu j))
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inl (Or.inr hx)))) (hle heta)
        · exact valueField_le_map _ (fun x hx => hv (Or.inl (Or.inr hx))) (hle hdel)
        · exact valueField_le_map _ (fun x hx => hv (Or.inr hx)) (hle hdel')
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨k, a, rfl⟩
          exact hr (om_mem_rootsField f k a)
      · refine le_map_of_qb_le _ (hle (h6 j hj hj')) fun x hx => a7 ?_
        rw [hK]
        exact mem_qb.2 ((le_iSup₂_of_le j ⟨hj, hj'⟩ le_rfl : δ.KPsi j ≤ ⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) hx)
    intro x hx
    obtain ⟨y, hy, e⟩ := hmap hx
    have hyx : y = x := T.fr.ι.injective e
    exact hyx ▸ hy

theorem oTied_of_ksExact : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre)
    (δ : FieldDat X.B.toPre), X.B.KsExact δ f → ∀ T : HostTied X.toD7, ∃ O : OTied X.toD7 T (Fr.at X f),
      O.pieces.rcf = qb T.fr.ι δ.ray ∧ O.pieces.MDel = qb T.fr.ι δ.M' := by
  intro hA hW X f δ hx T
  obtain ⟨P, -, hR, hM, hD, hK⟩ := _root_.GlobalTheory.SmallFieldPieces.exists_pieces hA hW X f δ T
  have hq := ksQ_eq X f δ hx T P hR hM hD hK
  refine ⟨⟨P, X.B.OtoLL_injective, fun x => ?_⟩, hR, hD⟩
  rw [hq]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨mem_qb.2 ?_, (X.toD7.O_int y).map T.jLL.toIntAlgHom⟩
    rw [T.embLL, ← show X.B.KsC = listField δ f from hx]
    exact ⟨_, (algebraMap (𝓞 X.B.Ks) X.B.Ks y).2, rfl⟩
  · rintro ⟨hxq, hi⟩
    have hz : T.fr.ι x ∈ X.B.KsC := by
      rw [show X.B.KsC = listField δ f from hx]
      exact hxq
    obtain ⟨w, hw, e⟩ := hz
    have hwx : T.jLL w = x := T.fr.ι.injective ((T.embLL w).trans e)
    subst hwx
    have hwi : IsIntegral ℤ w := (isIntegral_algHom_iff T.jLL.toIntAlgHom T.jLL.injective).1 hi
    obtain ⟨y, hy⟩ := X.B.O_full w hw hwi
    exact ⟨y, congrArg T.jLL hy⟩

end GlobalTheory.Mem.CyclotomicFieldContainment

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open Formalism.UG.P
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdComp

theorem eq_zero_of_valued_le {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (x : P.adicCompletion E) (h : ∀ n : ℕ, Valued.v x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log h0).symm⟩
  have h1 := h (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_eps_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) : adAt F w (afsplitEps E v) = 1 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 1))
    (fun n => by
      rw [he]
      exact hspec _ 1 w n (by rw [h, afsplitI_self, map_one, sub_self, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_one, map_one] at h0
  exact h0

theorem adAt_eps_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) : adAt F w (afsplitEps E v) = 0 := by
  have hspec : ∀ (a : FiniteAdeleRing (𝓞 F) F) (k : F) (P : HeightOneSpectrum (𝓞 E)) (n : ℕ),
      Valued.v (a (P.under (𝓞 F)) - algebraMap F _ k) ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (afIso F E (1 ⊗ₜ[F] a) P - algebraMap E _ (algebraMap F E k)) ≤ WithZero.exp (-(n : ℤ)) :=
    (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    simp only [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h0 := eq_zero_of_valued_le w (adAt F w (afsplitEps E v) - algebraMap E _ (algebraMap F E 0))
    (fun n => by
      rw [he]
      exact hspec _ 0 w n (by rw [afsplitI_ne v _ h, map_zero, sub_zero, map_zero]; exact zero_le'))
  rw [sub_eq_zero, map_zero, map_zero] at h0
  exact h0

theorem adAt_eps_mul_of_under (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) = v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = adAt F w z := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_under v w h, one_mul]

theorem adAt_eps_mul_of_ne (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    (h : w.under (𝓞 F) ≠ v) (z : AfE F E) : adAt F w (afsplitEps E v * z) = 0 := by
  have hm : adAt F w (afsplitEps E v * z) = adAt F w (afsplitEps E v) * adAt F w z := by
    unfold adAt; exact map_mul _ _ _
  rw [hm, adAt_eps_of_ne v w h, zero_mul]

theorem prV_zero_int_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (prV (E := E) v z = 0 ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → adAt F w z = 0) ∧ (prV (E := E) v z ∈ intV E v ↔ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → Valued.v (adAt F w z) ≤ 1) := by
  intro F E _ _ _ _ _ v z
  classical
  have hinj : ∀ x y : E ⊗[F] v.adicCompletion F, afsplitIE v x = afsplitIE v y → x = y := by
    intro x y hxy
    rw [← afsplit_prV_IE v x, hxy, afsplit_prV_IE]
  have hdec : afsplitIE v (prV (E := E) v z) = afsplitEps E v * z := afsplit_decomp v z
  have hz : ∀ w : HeightOneSpectrum (𝓞 E), adAt F w (0 : AfE F E) = 0 := by
    intro w; unfold adAt; exact map_zero _
  have hcomp : ∀ w : HeightOneSpectrum (𝓞 E),
      adAt F w (afsplitEps E v * z) = if w.under (𝓞 F) = v then adAt F w z else 0 := by
    intro w
    split_ifs with hw
    · exact adAt_eps_mul_of_under v w hw z
    · exact adAt_eps_mul_of_ne v w hw z
  refine ⟨⟨fun h0 w hw => ?_, fun h => ?_⟩, ⟨fun hint w hw => ?_, fun h => ?_⟩⟩
  · rw [← adAt_eps_mul_of_under v w hw z, ← hdec, h0, map_zero, hz]
  · apply hinj
    rw [hdec, map_zero]
    apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [hcomp, hz]
    split_ifs with hw
    · exact h w hw
    · rfl
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [← hdec]; exact afsplit_IE_int v _ hint
    rw [← adAt_eps_mul_of_under v w hw z]
    exact (mem_rInt_iff F E _).mp h1 w
  · have h1 : afsplitEps E v * z ∈ RInt F E := by
      rw [mem_rInt_iff]
      intro w
      change Valued.v (adAt F w (afsplitEps E v * z)) ≤ 1
      rw [hcomp]
      split_ifs with hw
      · exact h w hw
      · rw [map_zero]; exact zero_le'
    have h2 := afsplit_prV_int v _ h1
    rwa [← hdec, afsplit_prV_IE] at h2

end GlobalTheory.Mem.Col2.AdComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesOverPlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem conjO_piG_ne (hPr : Pr.Ok) (a : Fin 2) : X.conjO (Pr.piG a) ≠ 0 := by
  intro h0
  have := hPr.piG_norm a
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.2 (hPr.g_prime a).ne_zero) this.symm

theorem mem_vG_iff (hPr : Pr.Ok) (a : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Pr.vG a ↔ X.conjO (Pr.piG a) ∈ P.asIdeal := mem_divs (conjO_piG_ne hPr a) P

theorem g_mem_of_isOver {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)}
    (hv : IsOver v P) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ((Pr.g a : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [hv, Ideal.mem_comap, map_natCast] at h
  exact h

theorem eq_of_isOver (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) {P Q : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (hQ : Q ∈ Pr.vGs)
    (hPv : IsOver v P) (hQv : IsOver v Q) : Q = P := by
  rcases rll_over_cases hc hPv hQv with e | e
  · exact e
  exfalso
  have hPa := mem_vG_of_g_mem hPr hP (g_mem_of_isOver hPv h)
  have hQa := mem_vG_of_g_mem hPr hQ (g_mem_of_isOver hQv h)
  rw [mem_vG_iff hPr] at hPa hQa
  rw [e, mem_conjP] at hQa
  have h2 : cO X.E (X.conjO (Pr.piG a)) = Pr.piG a := RingOfIntegers.ext (star_star _)
  rw [h2] at hQa
  obtain ⟨x, y, hxy⟩ := hPr.piG_cop a
  refine P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ hQa) (Ideal.mul_mem_left _ _ hPa)

theorem exists_over_vGs (hc : Formalism.BasicNotions.CMData X.F X.E) (hPr : Pr.Ok) {a : Fin 2} {v : HeightOneSpectrum (𝓞 X.F)}
    (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal) : ∃ w : {w // w ∈ Pr.vGs}, IsOver v w.1 := by
  have h01 : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
  have hv : v ∈ plUnder X.F Pr.vGs := by
    rw [plUnder_vGs hc hPr v]
    rcases h01 a with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨P, hP, hPv⟩ := hv
  exact ⟨⟨P, hP⟩, hPv⟩

theorem isOver_of_under {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : P.under (𝓞 X.F) = v) :
    IsOver v P := by
  subst h
  rfl

theorem under_of_isOver {v : HeightOneSpectrum (𝓞 X.F)} {P : HeightOneSpectrum (𝓞 X.E)} (h : IsOver v P) :
    P.under (𝓞 X.F) = v :=
  HeightOneSpectrum.ext h.symm

end GlobalTheory.Mem.TypePrimes

namespace GlobalTheory.Mem.TypePrimes

variable {X : Fields} {Pr : Primes X}

theorem residue_natCast (hPr : Pr.Ok) {a : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG a)
    (c : 𝓞 X.E ⧸ w.asIdeal) : ∃ k : ℕ, c = k := by
  haveI : NeZero (Pr.g a) := ⟨(hPr.g_prime a).ne_zero⟩
  have e := (nonempty_equiv_zmod (𝓞 X.E ⧸ w.asIdeal) (hPr.g_prime a) (by
    rw [← hPr.vG_norm a w hw, Ideal.absNorm_apply, Submodule.cardQuot_apply])).some
  exact ⟨(e.symm c).val, by rw [← map_natCast e, ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]⟩

theorem vG_disjoint (hPr : Pr.Ok) : Disjoint (Pr.vG 0) (Pr.vG 1) := by
  rw [Finset.disjoint_left]
  intro w h0 h1
  have hc : IsCoprime ((Pr.g 0 : ℕ) : 𝓞 X.E) ((Pr.g 1 : ℕ) : 𝓞 X.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (hPr.g_prime 0) (hPr.g_prime 1)).2 hPr.g_ne)
  obtain ⟨x, y, hxy⟩ := hc
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hxy]
  exact add_mem (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h0)) (Ideal.mul_mem_left _ _ (g_mem_of_vG hPr h1))

theorem primes_over_places : ∀ (X : Fields) (Pr : Primes X) (hc : Formalism.BasicNotions.CMData X.F X.E), Pr.Ok →
    ∃ wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs},
      (∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h) ∧
      (∀ a v h, (∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = v → X.conjO (Pr.piG a) ∈ P.asIdeal →
          P = (wOf a v h).1) ∧ (wOf a v h).1.under (𝓞 X.F) = v ∧
        ∀ c : 𝓞 X.E ⧸ (wOf a v h).1.asIdeal, ∃ k : ℕ, c = k) ∧
      ∀ φ : {w // w ∈ Pr.vGs} → ℂ, ∏ w, φ w =
        ∏ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) := by
  intro X Pr hc hPr
  classical
  let wOf : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal → {w // w ∈ Pr.vGs} :=
    fun a v h => (exists_over_vGs hc hPr h).choose
  have hspec : ∀ a v h, IsOver v (wOf a v h).1 := fun a v h => (exists_over_vGs hc hPr h).choose_spec
  have h1 : ∀ a v h (w : {w // w ∈ Pr.vGs}), IsOver v w.1 ↔ w = wOf a v h := by
    intro a v h w
    constructor
    · intro hw
      exact Subtype.ext (eq_of_isOver hc hPr h (wOf a v h).2 w.2 (hspec a v h) hw)
    · rintro rfl
      exact hspec a v h
  have hin : ∀ a v h, (wOf a v h).1 ∈ Pr.vG a := fun a v h =>
    mem_vG_of_g_mem hPr (wOf a v h).2 (g_mem_of_isOver (hspec a v h) h)
  refine ⟨wOf, h1, fun a v h => ⟨?_, under_of_isOver (hspec a v h), residue_natCast hPr (hin a v h)⟩, ?_⟩
  · intro P hPu hP
    have hPa : P ∈ Pr.vG a := (mem_vG_iff hPr a P).2 hP
    exact eq_of_isOver hc hPr h (wOf a v h).2 (mem_vGs hPa) (hspec a v h) (isOver_of_under hPu)
  · intro φ
    let φ' : HeightOneSpectrum (𝓞 X.E) → ℂ := fun w => if hw : w ∈ Pr.vGs then φ ⟨w, hw⟩ else 1
    have hL : ∏ w, φ w = ∏ w ∈ Pr.vGs, φ' w := by
      rw [← Finset.prod_coe_sort Pr.vGs φ']
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [φ', dif_pos w.2]
    have hA : ∀ a : Fin 2, ∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h) =
        ∏ w ∈ Pr.vG a, φ' w := by
      intro a
      let f : HeightOneSpectrum (𝓞 X.F) → ℂ := fun v => if h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal then φ (wOf a v h) else 1
      have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 X.F)) (h : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal), φ (wOf a v h)) = ∏ᶠ v, f v := by
        refine finprod_congr fun v => ?_
        exact finprod_eq_dif _
      have hsupp : Function.mulSupport f ⊆ ((Pr.vG a).image fun w => w.under (𝓞 X.F) : Finset _) := by
        intro v hv
        have h' : (Pr.g a : 𝓞 X.F) ∈ v.asIdeal := by
          by_contra hn
          exact hv (by simp only [f, dif_neg hn])
        rw [Finset.coe_image]
        exact ⟨(wOf a v h').1, hin a v h', under_of_isOver (hspec a v h')⟩
      rw [e1, finprod_eq_prod_of_mulSupport_subset f hsupp, Finset.prod_image]
      · refine Finset.prod_congr rfl fun w hw => ?_
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        have hw' : w ∈ Pr.vGs := mem_vGs hw
        have e2 : wOf a (w.under (𝓞 X.F)) hg = ⟨w, hw'⟩ :=
          ((h1 a _ hg ⟨w, hw'⟩).1 (isOver_of_under rfl)).symm
        simp only [f, φ', dif_pos hg, dif_pos hw', e2]
      · intro w hw w' hw' he
        have hg : (Pr.g a : 𝓞 X.F) ∈ (w.under (𝓞 X.F)).asIdeal := by
          show (Pr.g a : 𝓞 X.F) ∈ Ideal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) w.asIdeal
          rw [Ideal.mem_comap, map_natCast]
          exact g_mem_of_vG hPr hw
        exact (eq_of_isOver hc hPr hg (mem_vGs hw) (mem_vGs hw') (isOver_of_under rfl) (isOver_of_under he.symm)).symm
    rw [hL, Fin.prod_univ_two, hA 0, hA 1]
    unfold Primes.vGs
    exact Finset.prod_union (vG_disjoint hPr)

end GlobalTheory.Mem.TypePrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTupQEqOneIff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Gen

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem parLev_of_Q (q : (levEnv V β L).Q) :
    Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) ∈ parLev D.sp.cm V.gram β L := q.2.1

def rTupQ : (levEnv V β L).Q →* G0 L.Pg L.r where
  toFun q := rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact rTup_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, map_mul]
    exact rTup_mul (parLev_of_Q V β L x) (parLev_of_Q V β L y)

theorem rTupQ_eq_one_iff (q : (levEnv V β L).Q) :
    rTupQ V β L q = 1 ↔ ((q : Bridge.Gf V)) ∈ (levEnv V β L).J := by
  constructor
  · intro h
    exact ⟨parLev_of_Q V β L q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

end Gen

end GlobalTheory.Mem.R3.RowAct
end
end

