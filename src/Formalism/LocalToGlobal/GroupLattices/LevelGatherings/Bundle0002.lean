module

public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle0001
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0001
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.JOInjective

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.CompletionIntegersIff
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

structure LocId (L : ColLevel R F E sp gp C A clsLat) (p nV : ℕ) (W Qq : Type) [CommRing W] [Field Qq] [Algebra W Qq] where
  pl : Fin nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}
  eQ : ∀ v : Fin nV, Qq ≃+* (pl v).1.adicCompletion F
  completion_integers_iff : ∀ v (x : Qq), x ∈ Set.range (algebraMap W Qq) ↔ eQ v x ∈ (pl v).1.adicCompletionIntegers F
  spl : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F
  spl_sig : ∀ w h x, spl w h (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (spl w h x)
  spl_alg : ∀ w h (a : w.adicCompletion F), spl w h ((1 : E) ⊗ₜ[F] a) = (a, a)
  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin R.k) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin R.k → w.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL w L.Lb, ∀ a, (spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin R.k) (w.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

namespace LocId

variable {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
  (I : LocId L p nV W Qq)

def iw (v : Fin nV) : E →+* Qq :=
  (I.eQ v).symm.toRingHom.comp ((RingHom.fst _ _).comp ((I.spl (I.pl v).1 (I.pl v).2).toRingHom.comp
    (inclE (F := F) ((I.pl v).1.adicCompletion F))))

def frQ (v : Fin nV) : GL (Fin R.k) Qq := bc (I.eQ v).symm.toRingHom (I.fr (I.pl v).1 (I.pl v).2)

end LocId

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

abbrev compL (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Type :=
  compC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)

abbrev gatOfLevel (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ) : GAtP p :=
  gatConst sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ (fun i => (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F))) e


set_option maxHeartbeats 2000000 in
def gatOfLevel_tie (L : ColLevel R F E sp gp C A clsLat) (hS : HidaSetting p n' W Qq O Kf ι σ j w) (nV r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F)) [Finite (compL L p)] (e : ℕ)
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w'.asIdeal →
      bc (prV (E := E) w') (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) = 1) :
    Formalism.L2.Herm.GLevTie L (gatOfLevel L hS nV r lam0 dom hk I ψ y e) where
  rk := hk
  pl := I.pl
  eQ := fun v w' h => h ▸ I.eQ v
  completion_integers_iff := by
    intro v w' h x
    subst h
    exact I.completion_integers_iff v x
  spl := I.spl
  spl_sig := I.spl_sig
  spl_alg := I.spl_alg
  fr := I.fr
  fr_lat := I.fr_lat
  yG := y
  yG_p := hyp
  yG_bij := ⟨fun a b hab => by
      have h1 := hy a; have h2 := hy b
      simp only at hab
      rw [← h1, ← h2]; exact hab, fun i => ⟨i, hy i⟩⟩
  gamI := fun i => (gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F))).subtype
  gamI_inj := fun i => Subtype.val_injective
  gamI_range := by
    intro i γ
    constructor
    · rintro ⟨g, rfl⟩
      exact g.2
    · intro h
      exact ⟨⟨γ, h⟩, rfl⟩
  act_eq := by
    intro i v w' h hw γ a b a' b' ha hb
    subst h
    have h1 := levC_act sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ
      (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) v γ
    have h2 : (((gatOfLevel L hS nV r lam0 dom hk I ψ y e).lev i).act v γ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) a b =
        (castGL hk Qq (((gatOfLevel L hS nV r lam0 dom hk I ψ y e).lev i).act v γ) :
          Matrix (Fin R.k) (Fin R.k) Qq) a' b' := by
      rw [castGL_apply]
      have ea : a = Fin.cast hk.symm a' := Fin.ext ha
      have eb : b = Fin.cast hk.symm b' := Fin.ext hb
      rw [ea, eb]
    have h3 : (I.frQ v)⁻¹ * bc (I.iw v) (gamMat sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)
          (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) γ) * I.frQ v =
        bc (I.eQ v).symm.toRingHom ((I.fr (I.pl v).1 (I.pl v).2)⁻¹ *
          bc ((RingHom.fst _ _).comp (I.spl (I.pl v).1 (I.pl v).2).toRingHom)
            (bc (inclE (F := F) ((I.pl v).1.adicCompletion F)) (gamMat sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p)
              (y i : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) γ)) * I.fr (I.pl v).1 (I.pl v).2) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    show I.eQ v _ = _
    rw [h2, h1, h3]
    show I.eQ v ((I.eQ v).symm _) = _
    rw [RingEquiv.apply_symm_apply]
    rfl

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.StdSub
section
noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable {p n' : ℕ} [hp : Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem settingStd_iso (hD : HidaSetting p n' W Qq O Kf ι σ j w) (eW : WQ p n' ≃+* W) (eQ : QQ p n' ≃+* Qq)
    (heq : ∀ x, eQ (algebraMap (WQ p n') (QQ p n') x) = algebraMap W Qq (eW x)) :
    UnramifiedQuadraticSetting p n' W Qq (OO p n') (KO p n') ((iota p n').comp (eQ.symm : Qq →+* QQ p n')) σ
      ((jO p n').comp (eW.symm : W →+* WQ p n')) (wU p n') := by
  obtain ⟨hS, hirr, hcard, hsq⟩ := settingStd p n' hD.five_le hD.two_le hD.even
  refine ⟨?_, hirr, hcard, hsq⟩
  exact
    { prime := hD.prime, five_le := hD.five_le, two_le := hD.two_le, even := hD.even, frac_alt := hD.frac_alt,
      frac_O := hS.frac_O, p_unif := hD.p_unif, res_card := hD.res_card, eq_sum_herm_smul_frame_of_inW := hD.eq_sum_herm_smul_frame_of_inW,
      frob := hD.frob, period := hD.period,
      ι_comp := fun x => by
        have h1 := hS.ι_comp (eW.symm x)
        have h2 := heq (eW.symm x)
        simp only [RingEquiv.apply_symm_apply] at h2
        simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
        rw [← h2, RingEquiv.symm_apply_apply, h1],
      finite := hS.finite.comp (RingHom.Finite.of_surjective _ eW.symm.surjective),
      complete_O := hS.complete_O,
      w_sq := hS.w_sq }

theorem stdSub_of_iso (hD : HidaSetting p n' W Qq O Kf ι σ j w) (eW : WQ p n' ≃+* W) (eQ : QQ p n' ≃+* Qq)
    (heq : ∀ x, eQ (algebraMap (WQ p n') (QQ p n') x) = algebraMap W Qq (eW x))
    (X : ExtOf (OO p n') (KO p n') O Kf)
    (hι : ∀ y, ι (eQ y) = X.φK (iota p n' y)) (hj : ∀ x, j (eW x) = X.φ (jO p n' x)) (hw : X.φ (wU p n') = w) :
    ∃ (Os Ks : Type) (_ : CommRing Os) (_ : IsDomain Os) (_ : IsDiscreteValuationRing Os) (_ : Field Ks)
      (_ : Algebra Os Ks) (ιs : Qq →+* Ks) (js : W →+* Os) (ws : Os) (φ : Os →+* O) (φK : Ks →+* Kf),
      (∀ x : Os, φK (algebraMap Os Ks x) = algebraMap O Kf (φ x)) ∧ φ.Finite ∧
      UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws ∧ φK.comp ιs = ι ∧ φ.comp js = j ∧ φ ws = w := by
  refine ⟨OO p n', KO p n', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (iota p n').comp (eQ.symm : Qq →+* QQ p n'), (jO p n').comp (eW.symm : W →+* WQ p n'), wU p n', X.φ, X.φK,
    X.comm, X.fin, settingStd_iso hD eW eQ heq, ?_, ?_, hw⟩
  · ext y
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← hι, RingEquiv.apply_symm_apply]
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [← hj, RingEquiv.apply_symm_apply]

end Formalism.L2.G
end
end

