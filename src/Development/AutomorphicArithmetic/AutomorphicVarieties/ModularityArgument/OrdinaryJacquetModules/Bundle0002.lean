module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdJac
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.AtLOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Ord

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A w)

def AtLT (r : Dec (F := L) A →* GL (Fin n) (Qbar l)) (lam : Wt L l n) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) : Prop :=
  ∀ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) →
    (∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) → Nonempty (σ.ρ.Equiv (PS ω)) →
  ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → Lev.AbW (rc (algNorm σ)) →
    DRat ι h r (fun τ => Finset.univ.val.map fun j => htW lam j τ) fun s => (rc (algNorm σ)).charPol s

def AtLOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (A : ValuationSubring Ω) (w : Plc L) (h : IsPlaceOver A w) (r : G L Ω →* GL (Fin n) (Qbar l)) (HT : (L →+* Qbar l) → Multiset ℤ)
    (τ : SmIrr (GLw n w)) (lam : Wt L l n), (GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred) → Win.HasHTAt r HT w) →
    Win.LocGlobT ι r w τ → (∀ j : W.Emb l w, (HT (j.1.comp (algebraMap L _))).map (fun k : ℤ => (k : ℂ)) =
      (infOfWeight (lam (j.1.comp (algebraMap L _))).dual).map fun z => ((n : ℂ) - 1) / 2 - z) →
    AtLT ι h (r.comp (Dec (F := L) A).subtype) lam τ

end UpperTheory.V.Z.Ord

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FiniteOverL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem finite_over_l (L : Type) [Field L] [NumberField L] (l : ℕ) [hl : Fact l.Prime] :
    {w : Plc L | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    simp [hl.out.ne_zero]
  exact (Ideal.finite_factors h0).subset fun w hw =>
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hw)

private theorem split_l {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Vl l L) : IsSplitAt (s.w v.1) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
    (HeightOneSpectrum.ext (Ideal.ext fun x =>
      (show _ ↔ _ from (s.hw v.1) (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v.1 x)))

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ι : Qbar l ≃+* ℂ)

private def PO (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q τ₀).Part ι lam ξ) : Prop :=
  Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
    Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)

private theorem po_of (hP : Af.HypothesesH) (hn : 1 ≤ n) {lam : Wt L l n} {d : ℕ} {ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ}
    (Y : (hset Q τ₀).Part ι lam ξ) (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ)
    (hcomp : ∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      Af.LocGlob ι (Y.r.comp V.pr) w τ) : PO Q τ₀ ι lam d ξ Y := fun hi => by
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, p1, p2, p3, p4⟩ := linkU hP L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ (Y.r.comp V.pr) hc hi
    ((Filter.eventually_cofinite.2 (by simpa using finite_over_l L l)).mono fun w hw hsp τ hτc B hB =>
      Af.satFrob hP.toClassicalTheorems L Ω l ι n _ hc w hw τ B hB fun A h rc hrc => (hLG w hsp τ hτc A h rc hrc).1 hw)
  exact ⟨π, p1, p2, p3, fun v => p4 _ (split_l s v) _ (hcomp v)⟩

end

private theorem autPO (hP : Af.HypothesesH) (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l)
    (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (hτ : TypeFor r ι τ₀) :
    AutY (hset Q τ₀) ι (PO Q τ₀ ι) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let lift := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
    let j := lift (RingHom.id (ResidueField c.O))
    let τ := (Perfection.teichmuller l (maximalIdeal c.O)).comp j.toMonoidHom
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x :=
      (Perfection.mk_teichmuller (j x)).trans
        (RingHom.congr_fun (lift.symm_apply_apply (RingHom.id (ResidueField c.O))) x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hmap : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin m) f) := by
      intro A B hAB
      apply Units.ext
      apply Matrix.ext
      intro i j
      exact hf (congrArg (fun M : GL (Fin m) ℂ => (M : Matrix (Fin m) (Fin m) ℂ) i j) hAB)
    rw [← MonoidHom.ker_comp_of_injective τ₀ _ hmap]
    exact (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, -, hcomp, hLG⟩ := partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PO Q τ₀ ι lam d ξ Y} => Y.1.Y)
      ⟨Y, po_of Q τ₀ ι hP hn Y σ.1 σ.2 hcomp hLG⟩

theorem UpperTheory.V.Z.Ord.autUO :
    Af.HypothesesH → AutUO := fun hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ =>
  autPO hP l L Ω s n hn V Q c r ι m τ₀ hτ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FlagOfRel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp

private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have rep_single {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B] (g : T) (r : B) :
      W.GDet.repAlg (R) B (MonoidAlgebra.single g r) = r • (R g).map (algebraMap A B) := by
    unfold W.GDet.repAlg
    rw [MonoidAlgebra.lift_single]
    rfl
  have rep_map {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      W.GDet.repAlg (R) A[X] (MonoidAlgebra.mapRingHom T (algebraMap A A[X]) y) =
        (W.GDet.repAlg (R) A y).map (algebraMap A A[X]) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => simp [MonoidAlgebra.of_apply, rep_single R]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      ext i j
      simp
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by
        rw [Algebra.smul_def]
        rfl
      have hm : MonoidAlgebra.mapRingHom T (algebraMap A A[X]) (MonoidAlgebra.single 1 r)
          = MonoidAlgebra.single 1 (algebraMap A A[X] r) := by
        ext g
        simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, rep_single R, rep_single R, map_one]
      congr 1
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have rep_chi {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      (W.GDet.ofRep (R)).chi y = (W.GDet.repAlg (R) A y).charpoly := by
    unfold W.GDet.chi
    change (W.GDet.repAlg (R) A[X] _).det = _
    rw [← Polynomial.algebraMap_eq, map_sub, rep_single R, rep_map R, map_one]
    rw [Matrix.charpoly]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]
  have rep_trace {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A T) :
      (W.GDet.ofRep (R)).tr y = (W.GDet.repAlg (R) A y).trace := by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold W.GDet.tr W.GDet.lam
    rw [rep_chi R, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  have rep_chi_single {T : Type} [Group T] (R : T →* Matrix (Fin n) (Fin n) A) (g : T) :
      (W.GDet.ofRep (R)).chi (MonoidAlgebra.single g 1) = (R g).charpoly := by
    rw [rep_chi R, rep_single R]
    simp
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [rep_trace (W.mat ρ), rep_trace (W.mat ρ)] at e
      rw [rep_trace (W.mat ρ), mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, rep_chi_single (W.mat ρ), rep_chi_single (W.mat ρ₀), hm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdScal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

private theorem char_at {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {F : M} (hne : F ≠ 0) (h : ∀ t, ∃ a : ℂ, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t)
        rw [map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩

private theorem uOp_at {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  intro F hF
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]

private theorem Uc_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))

private theorem local_exp (hJ : OrdJac) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    {F : M} (hFY : F ∈ Y) (hF0 : F ≠ 0) (e : ℕ) (f : Fin n → Uo k → ℂ)
    (hN : F ∈ fixd ρ (glIwa k n).N) (hNm : F ∈ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (a : ℕ → ℂ)
    (ha : ∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp ρ (al k n (j + 1)) F = a (j + 1) • F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient σ.ρ (PS ω) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧ ∀ j : Fin n, psEig ω (j + 1) = a (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  obtain ⟨p, hp, hp0⟩ := isoSep hσ hFY hF0
  have hpe : p F ∈ (glIwa k n).eig σ.ρ e φ :=
    ⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu],
      fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩
  obtain ⟨ω, h1, h2, h3, h4⟩ := hJ k n σ.V σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j =>
      ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans
        ((congrArg p (ha j).2).trans (map_smul p _ _))⟩
  exact ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩

theorem UpperTheory.V.Z.Ord.ordScal : GlobalTheory.Mem.LiteralAutomorphy.LitN → OrdScal := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb
  classical
  have hN : F ∈ fixd (H.atV d v) (glIwa _ n).N := fun u hu =>
    hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun u hu =>
    hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun i y => by
    have := hF.2.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun j =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·)
      (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)
  have hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0 := fun j h0 => by
    have := (hb j).2
    rw [hop j, h0, inv_zero, zero_smul] at this
    exact smul_ne_zero (hb j).1 hF0 this.symm
  let a : ℕ → ℂ := fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)
  have ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j := fun j => by
    have h : (j : ℕ) + 1 - 1 < n := by simpa using j.2
    simp only [a, dif_pos h]
    congr 2
  obtain ⟨ω, h1, h2, h3, h4⟩ := local_exp (UpperTheory.V.Z.Ord.ordJac hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT
    (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j =>
      ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, by
        have h := (hop j).symm.trans (hb j).2
        rw [inv_smul_eq_iff₀ (hl j), smul_smul] at h
        rw [ha j]
        exact h⟩
  exact ⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩
end

