module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
public import Formalism.LocalToGlobal.Columns.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPinned
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.PinW

theorem valsRoots (K : Ctx) : large₂ K fun B f T => ∀ (px : PreX B.toPre) (I : ColIn B px), I.Ok →
    I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} → Set.range I.xi = T.set f →
    (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => GlobalTheory.Mem.Col2.InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ z hz => hZ B Ξ z hz, fun B f T _ hH _ _ => ?_⟩
  intro px I h hS hxi
  refine ⟨fun a P _ => ⟨_, (h.xi_reads a _).symm⟩, fun a P hP => ?_⟩
  have hm : I.xi a ∈ T.set f := hxi ▸ Set.mem_range_self a
  have ht := GlobalTheory.Mem.Col2.InEx.isTwist_of_mem_set B f T _ hm
  have hf := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
  have hold := gZ B.toPre _ hf B.LL B.embLL (fun z hz => B.mem_LLC.1 (hH.2 z hz)) _ hm ht.1
  have ht' : Chr.IsTwist B.host I.S (I.xi a) := by rw [hS]; exact ht
  obtain ⟨P', a1, a2⟩ := GlobalTheory.Mem.Col2.InEx.exists_ram_of_mem_QE B h.sel_ok (I.tup a) ht' (h.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := (hold.2 P' a1).2
  refine ⟨ζ, ?_⟩
  rw [pow_one] at hζ
  have e : Nat.card (𝓞 B.fields.E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, a2]
  exact hζ

theorem step_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) (fun K B f T => ∃ w : ColW B f T, Pinned K B f T w) := by
  have e1 := evG_of_ev (ev_preX_frame h2b)
  have e2 := evG_of_ev GlobalTheory.Mem.Col2.TwIdxEx.evLg_canonical
  have e3 := evG_all fun K => (valsRoots K).inter (GlobalTheory.Mem.Col2.InEx.lg_colIn K)
  refine ((e1.inter e2).inter e3).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hfr, h41⟩, hv⟩ := H
  refine (h41.inter hv).imp fun B f T hO G hk _ _ => ?_
  obtain ⟨H, V, Lc⟩ := G
  obtain ⟨⟨δ, hδ⟩, hp⟩ := hk
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := GlobalTheory.T.exists_half_selection_split_places_base B
  obtain ⟨X, I, hok, hpins, htw, hjets, hsel', hC, hS, hxi, hval⟩ := H hp (hfr _ hO).1 Pv hsel
  obtain ⟨hv1, hv2⟩ := V X I hok hS hxi
  subst hsel'
  exact ⟨⟨X, I, hok, hC, hS, hxi, hpins, GlobalTheory.Mem.Col2.TC.laws_of_ok I hok, StepZero.law0 I hok _, δ, hδ, Lc.2.2,
      fun C W V S N G => (hval C W V S N G).1⟩,
    ⟨⟨htw, hjets, GlobalTheory.Mem.FieldsLaws.fields_ok B, habove, hhalf, d, ⟨hd1, hd2⟩, hv1, hv2⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.PinW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepQOfReindex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartQ

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stepQ_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Formalism.L2.Forms.StepLevel F E σ J T f bad) (H0 : Formalism.L2.Herm.StepLevel hc S gp T f)
    (hQ : ∀ v ∈ Q, ((T : ℕ) : 𝓞 F) ∉ v.asIdeal ∧ ∀ j, ((gp j : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hLb : K.Lb = reL h H0.Lb) (hU : ∀ v, v ∉ Q → K.Uloc v = (H0.Uloc v).map (reGL h _).toMonoidHom) :
    ∃ L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q, L.Lb = H0.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  simp only [GlobalTheory.HermTransport.reL_refl'] at hLb
  simp only [GlobalTheory.HermTransport.reGL_refl_hom', Subgroup.map_id] at hU ⊢
  have hgQ : ∀ (i : Fin 2) v, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun i v hv hvQ => (hQ v hvQ).2 i hv
  have hTQ : ∀ v, ((T : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun v hv hvQ => (hQ v hvQ).1 hv
  let L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q :=
    { Lb := H0.Lb
      Lb_fin := H0.Lb_fin
      Lb_span := H0.Lb_span
      Lb_int := H0.Lb_int
      Lb_dual := H0.Lb_dual
      Lb_index := H0.Lb_index
      Uloc := K.Uloc
      Uloc_lev := fun v => hLb ▸ K.Uloc_lev v
      Uloc_hyp := fun v h0 h1 hT hvQ => (hU v hvQ).trans (H0.Uloc_hyp v h0 h1 hT)
      Uloc_g := fun i v hv x hx => (hU v (hgQ i v hv)) ▸ H0.Uloc_g i v hv x hx
      UlocAlt := fun v hv x => (hU v (hTQ v hv)) ▸ H0.UlocAlt v hv x
      Uloc_Q := fun v _ => by
        obtain ⟨N, hN, hx⟩ := _root_.GlobalTheory.OpenPrinc.open_princ hc.sig S.gram K v
        exact ⟨N, hN, fun x hx' => hx x (hLb ▸ hx'.1) (hLb ▸ hx'.2)⟩
      U := K.U
      U_eq := K.U_eq }
  exact ⟨L, rfl, fun v => rfl, rfl⟩

end Gen

theorem chartTie_toQ : ∀ {D : D7} {T : ℕ} (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) {i : ℕ} (hm : i ≤ D.R.m) {cl : Type} (st : cl → Type) [∀ c, Group (st c)] (lt : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V) (K : LevelChart D T (badQ D Q) i hm st (fun c => latCrd D i hm (lt c))) (H0 : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T D.R.f), (∀ v ∈ Q, ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ j, ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) → K.lev.Lb = reL (rankN D i hm) H0.Lb → (∀ v, v ∉ Q → K.lev.Uloc v = (H0.Uloc v).map (reGL (rankN D i hm) _).toMonoidHom) → ∃ (L : Formalism.L2.Herm.StepLevelQ D.sp.cm (D.sp.X i) D.host.g T D.R.f Q) (C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U st lt), L.Lb = H0.Lb ∧ SameCar (rankN D i hm) L.Lb K.lev.Lb L.Uloc K.lev.Uloc L.U K.lev.U (fun c => (C.y c).1) (fun c => (K.y c).1) (fun c s => (C.stabI c s).1) (fun c s => (K.stabI c s).1) := by
  intro D T Q i hm cl st _ lt K H0 hQ hLb hU
  obtain ⟨L, hL, hUloc, hUU⟩ := GlobalTheory.ChartQ.stepQ_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) (σ := sigD D) rfl
    (fun a b => rfl) Q K.lev H0 hQ hLb hU
  obtain ⟨C, hy, hst⟩ := GlobalTheory.HermTransport.classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) rfl (fun a b => rfl)
    (Equiv.refl cl) lt K.y K.y_bij (fun c x => by rw [← GlobalTheory.HermTransport.latCrd_eq_reL]; exact K.y_lat c x) K.stabI
    K.stabI_inj K.stabI_range L.Lb L.U (hL ▸ hLb) hUU
  exact ⟨L, C, hL, ⟨hL ▸ hLb, hUloc, hUU, fun c => hy c, fun c s => hst c s⟩⟩

end GlobalTheory.ChartQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedUnitaryAdelicIntegralWithInverse
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.IntSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}

theorem val_entry_le {P : HeightOneSpectrum (𝓞 E)} {G : Sp E n ≃ₗ[E] Sp E n} (hG : G ∈ Formalism.L2.Col.GLint E n P) (i j : Fin n) :
    Valued.v (algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' G.toLinearMap i j)) ≤ 1 := by
  have he : (Pi.single j 1 : Sp E n) ∈ Formalism.L2.Col.stdAt E n P := by
    refine Formalism.L2.Col.le_locP P _ ((mem_stdLat _).2 fun l => ?_)
    rw [Pi.single_apply]
    split_ifs
    exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
  have hGe : G (Pi.single j 1) ∈ Formalism.L2.Col.stdAt E n P := (hG (Pi.single j 1)).2 he
  have hint : Formalism.L2.Col.IntAt P (G (Pi.single j 1) i) := by
    obtain ⟨s, hs, hsx⟩ := (Formalism.L2.Col.mem_locP P _ _).1 hGe
    obtain ⟨r, hr⟩ := (mem_stdLat _).1 hsx i
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  have e : LinearMap.toMatrix' G.toLinearMap i j = G (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    congr 2
  rw [e]
  exact LevRead.hasRes_le (ReadBad.hasRes_redP hint)

theorem val_away {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)}
    (hu : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    Valued.v (adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1 := by
  have hne : Q.under (𝓞 F) ≠ v := fun e => hQ (e ▸ (rfl : Formalism.L2.Col.IsOver (Q.under (𝓞 F)) Q))
  have h1 : bc (prV (E := E) (Q.under (𝓞 F))) u = bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) := by
    rw [map_one]; exact hu _ hne
  have h2 : adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
    apply ChTwRead.adAt_congr_prV
    exact congrArg (fun g => g.1 i j) h1
  rw [h2, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem inv_entry (hc : CMData F E) {u : GL (Fin n) (AfE F E)} (hu : u ∈ Formalism.L2.Herm.UstdAf hc n) (i j : Fin n) :
    ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) j i =
      sigR hc.sig (FiniteAdeleRing (𝓞 F) F) ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have h : ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) =
      1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) := by
    have hu' : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) *
        ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *
        (u : Matrix (Fin n) (Fin n) (AfE F E)) =
        (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hu
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu'
    have he : 1 + cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) ((u : Matrix (Fin n) (Fin n) (AfE F E)) - 1) =
        cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) := by
      unfold cT
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one, add_sub_cancel]
    rw [he]
    calc ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))
        = (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (u : Matrix (Fin n) (Fin n) (AfE F E)) *
            (u : Matrix (Fin n) (Fin n) (AfE F E))) *
            ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) := by rw [hu', Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h' := congrFun (congrFun h j) i
  refine h'.trans ?_
  unfold cT
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one,
    add_sub_cancel]
  rfl

theorem adAt_inv {u : GL (Fin n) (AfE F E)} {P : HeightOneSpectrum (𝓞 E)} {g : Sp E n ≃ₗ[E] Sp E n}
    (h : ∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) (r s : Fin n) :
    adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' (g⁻¹).toLinearMap r s) := by
  have e1 : (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) =
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) := by
    exact Matrix.ext fun r s => h r s
  have e2 : (adAt F P).mapMatrix ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *
      (adAt F P).mapMatrix (u : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e3 : (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' g.toLinearMap) *
      (algebraMap E (P.adicCompletion E)).mapMatrix (LinearMap.toMatrix' (g⁻¹).toLinearMap) = 1 := by
    rw [← map_mul, ← LinearMap.toMatrix'_comp]
    have : g.toLinearMap ∘ₗ (g⁻¹).toLinearMap = LinearMap.id := by
      exact LinearMap.ext fun y => g.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id, map_one]
  rw [e1] at e2
  have e4 := left_inv_eq_right_inv e2 e3
  exact congrFun (congrFun e4 r) s

theorem int_of_supported : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E := by
  intro F E _ _ _ _ _ _ hc n u hu v P hv hsup g hg hcomp i j
  have hsup' : ∀ v', v' ≠ v → bc (prV (E := E) v') u⁻¹ = 1 := fun v' h => by rw [map_inv, hsup v' h, inv_one]
  have a1 : ∀ r s, Valued.v (adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [hcomp]; exact val_entry_le hg r s
  have a2 : ∀ r s, Valued.v (adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)) ≤ 1 := fun r s => by
    rw [adAt_inv hcomp]; exact val_entry_le (inv_mem hg) r s
  refine ⟨(mem_rInt_iff F E _).2 fun Q => ?_, (mem_rInt_iff F E _).2 fun Q => ?_⟩
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a1 i j
      · rw [← valued_sigR hc, ← inv_entry hc hu]
        exact a2 j i
    · exact val_away hsup hQ i j
  · show Valued.v (adAt F Q _) ≤ 1
    by_cases hQ : Formalism.L2.Col.IsOver v Q
    · rcases rll_over_cases hc hv hQ with rfl | rfl
      · exact a2 i j
      · rw [← valued_sigR hc, ← inv_entry hc (inv_mem hu), inv_inv]
        exact a1 j i
    · exact val_away hsup' hQ i j

end GlobalTheory.Mem.Col2.AdT.IntSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3

theorem twArgs_lev : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HEq a.x.R.C (Top.Fr.at (w.st Z) f) ∧ HEq a.x.R.Pg (B.primes w.px).vGs ∧ (∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ → HEq (a.x.R.Q (a.x.Y.tupT μ)) (w.I.Q μ) ∧ HEq (a.x.R.toLevCh.xiH (a.x.Y.tupT μ)) (w.I.xi μ)) ∧ (∀ i p v s, a.x.R.EEp3 p ≠ ⊥ → ∃ p' s', HEq p' p ∧ HEq s' s ∧ a.x.R.lam3 i s p v = t.r.z.R.lam3 i s' p' v) := by
  intro K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tupT = t.r.Y.tupT := eq_of_heq htupT
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq_of_eq (t.r.z.lev.C.trans (congrArg _ w.C_eq))
  · exact heq_of_eq t.r.z.lev.Pg
  · change ∀ μ, Formalism.IndefR.RecTie.Used0 (w.st Z).toD7 μ →
      HEq (t.r.z.R.Q (Y.tupT μ)) (w.I.Q μ) ∧ HEq (t.r.z.R.xiH (Y.tupT μ)) (w.I.xi μ)
    intro μ hμ
    have hix : ixOf w.I (usedOf w.I T Wt) (t.r.Y.tupT μ) = μ := (t.r.tup_ix _).symm.trans (t.r.Y.tupTie μ hμ)
    rw [hT', t.r.z.lev.Q, t.r.z.lev.xiH, hix]
    exact ⟨HEq.rfl, HEq.rfl⟩
  · intro i p v s hp
    refine ⟨p, s, HEq.rfl, HEq.rfl, ?_⟩
    change t.r.z.R.EEp3 p ≠ ⊥ at hp
    change lam i s p v = t.r.z.R.lam3 i s p v
    exact lam_eq i s p v hp


end GlobalTheory.Mem.R3
end

