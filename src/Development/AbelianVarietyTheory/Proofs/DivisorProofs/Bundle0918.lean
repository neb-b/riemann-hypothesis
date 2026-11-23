module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0840
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousBdGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeoLevelActionIffGeoAct
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

open CategoryTheory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

end Rel

section Half

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

theorem exists_half (a : Dw.La) : ∃ b ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ b = (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a := by
  have h : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime, Submodule.top_smul]; trivial
  rw [Submodule.sup_smul] at h
  obtain ⟨x, hx, b, hb, rfl⟩ := Submodule.mem_sup.1 h
  refine ⟨b, hb, ?_⟩
  rw [map_add (f := _), show (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).2 hx, zero_add]

theorem map_mem_smul_top {I : Ideal (𝓞 E)} (f : Dw.La →ₗ[𝓞 E] Dw.La) {a : Dw.La}
    (ha : a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)) : f a ∈ I • (⊤ : Submodule (𝓞 E) Dw.La) := by
  have h := Submodule.mem_map_of_mem (f := f) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem half_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have h1 := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
  have := l.three_le
  have h2 : l.M = 0 := by exact_mod_cast h1
  omega

theorem graph_iff {r : ℕ} (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb))
    (C : Dw.La → Dw.La → Prop)
    (hC : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), C a a' ↔
        φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a') = Y.mulVec (φ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a)))
    (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) :
    (∀ q, φ (γ q) = Y.mulVec (φ q)) ↔
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) → C a a' := by
  constructor
  · intro hg a ha a' ha' e
    rw [hC a ha a' ha', e, hg]
  · intro hg q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha, e⟩ := exists_half (l := l) x
    have ha' := map_mem_smul_top (liftLa γ) ha
    rw [← e, ← liftLa_spec]
    exact (hC a ha _ ha').1 (hg a ha _ ha' (liftLa_spec _ a))

end Half

theorem exists_coord_of {O S La : Type} [CommRing O] [CommRing S] [AddCommGroup La] [Module O La] (o : O →+* S)
    {I J : Ideal O} {M r : ℕ} (hIJ : I * J = Ideal.span {(M : O)}) (hco : I ⊔ J = ⊤) (π : S →+* O ⧸ I)
    (hπ : ∀ a, π (o a) = Ideal.Quotient.mk I a) (hπ0 : ∀ s, π s = 0 ↔ s ∈ I.map o) (ρ : La →+ (Fin r → S))
    (hlin : ∀ (b : O) (a : La), ρ (b • a) = o b • ρ a)
    (hsur : ∀ s : Fin r → S, ∃ (a : La) (s' : Fin r → S), s = ρ a + M • s')
    (hker : ∀ a : La, (∀ i, ρ a i ∈ I.map o) → a ∈ I • (⊤ : Submodule O La)) :
    ∃ φ : (La ⧸ (I • (⊤ : Submodule O La))) ≃ₗ[O] (Fin r → O ⧸ I), ∀ y : Matrix (Fin r) (Fin r) S,
      ∀ a ∈ J • (⊤ : Submodule O La), ∀ a' ∈ J • (⊤ : Submodule O La),
        (∃ s : Fin r → S, y.mulVec (ρ a) - ρ a' = M • s) ↔
          φ ((I • (⊤ : Submodule O La)).mkQ a') = (y.map π).mulVec (φ ((I • (⊤ : Submodule O La)).mkQ a)) := by
  have hMb : (M : O) ∈ I :=
    Ideal.mul_le_left (I := I) (J := J) (by rw [hIJ]; exact Ideal.mem_span_singleton_self _)
  have hπM : ∀ s : S, π (M • s) = 0 := fun s => (hπ0 _).2 (by
    rw [nsmul_eq_mul, ← map_natCast o]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hMb))
  have hmem : ∀ K : Ideal O, ∀ a ∈ K • (⊤ : Submodule O La), ∀ i, ρ a i ∈ K.map o := fun K a ha i => by
    refine Submodule.smul_induction_on (p := fun a => ρ a i ∈ K.map o) ha ?_ ?_
    · intro b hb x _
      rw [hlin]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hb)
    · intro x y hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
  let f : La →ₗ[O] (Fin r → O ⧸ I) :=
    { toFun := fun a i => π (ρ a i)
      map_add' := fun a b => funext fun i => by simp
      map_smul' := fun b a => funext fun i => by
        rw [hlin, Pi.smul_apply, smul_eq_mul, map_mul, hπ]
        rfl }
  have hk : LinearMap.ker f = I • (⊤ : Submodule O La) := by
    ext a
    rw [LinearMap.mem_ker]
    exact ⟨fun h => hker a fun i => (hπ0 _).1 (congrFun h i), fun h => funext fun i => (hπ0 _).2 (hmem _ a h i)⟩
  have hs : Function.Surjective f := fun x => by
    choose b hb using fun i => Ideal.Quotient.mk_surjective (x i)
    obtain ⟨a, s', e⟩ := hsur fun i => o (b i)
    refine ⟨a, funext fun i => ?_⟩
    have := congrArg π (congrFun e i)
    rw [Pi.add_apply, map_add (f := _), Pi.smul_apply, hπM, add_zero, hπ, hb] at this
    exact this.symm
  refine ⟨(Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs), fun y a ha a' ha' => ?_⟩
  change _ ↔ f a' = (y.map π).mulVec (f a)
  have hv : ∀ i, ((y.map π).mulVec (f a)) i = π (y.mulVec (ρ a) i) := fun i =>
    (RingHom.map_mulVec π y (ρ a) i).symm
  constructor
  · rintro ⟨s, e⟩
    funext i
    have := congrArg π (congrFun e i)
    rw [Pi.sub_apply, map_sub, Pi.smul_apply, hπM, sub_eq_zero] at this
    rw [hv]
    exact this.symm
  · intro e
    have h1 : ∀ i, (y.mulVec (ρ a) - ρ a') i ∈ Ideal.span {(M : S)} := fun i => by
      have hb : (y.mulVec (ρ a) - ρ a') i ∈ I.map o := by
        rw [← hπ0, Pi.sub_apply, map_sub, sub_eq_zero, ← hv, ← e]
        rfl
      have hc : (y.mulVec (ρ a) - ρ a') i ∈ J.map o := by
        refine sub_mem ?_ (hmem _ a' ha' i)
        exact Ideal.sum_mem _ (t := Finset.univ) (f := fun k => y i k * ρ a k) fun k _ =>
          Ideal.mul_mem_left _ _ (hmem _ a ha k)
      have hco' : I.map o ⊔ J.map o = ⊤ := by rw [← Ideal.map_sup, hco, Ideal.map_top]
      have hi := Submodule.mem_inf.2 ⟨hb, hc⟩
      rwa [← Ideal.mul_eq_inf_of_coprime hco', ← Ideal.map_mul, hIJ, Ideal.map_span, Set.image_singleton,
        map_natCast] at hi
    choose s hs using fun i => Ideal.mem_span_singleton'.1 (h1 i)
    exact ⟨s, funext fun i => by rw [← hs i, Pi.smul_apply, nsmul_eq_mul, mul_comm]⟩

variable {D : D7}

section Dict

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

def Cong (V : HSp D) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (M : ℕ) (κ : GA D V) (a a' : Dw.La) : Prop :=
  ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w


set_option maxHeartbeats 800000 in
theorem exists_coord (l : Level H) (V : HSp D) {r : ℕ} (hr : V.rank = r) (β : GL (Fin r) (EAf D))
    (hβ : LatticeBasisLifts.IsLatBasis V hr β) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) :
    ∃ φ : LaMod Dw l ≃ₗ[𝓞 D.host.E] (Fin r → 𝓞 D.host.E ⧸ l.Mb),
      ∀ (κ : GA D V) (h : LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        Cong V ι l.M κ a a' ↔
          φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a') =
            ((Formalism.L2.DIV.pullFr β ⟨_, h⟩).1.map (resI D.host.F l.Mb (half_ne_bot l))).mulVec
              (φ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a)) := by
  obtain ⟨ρ, hlin, hsur, hker, hcong⟩ := _root_.GlobalTheory.GeoActCompare.exists_lattice_coord D V r hr β hβ Dw.La ι hι l.M (by have := l.three_le; omega)
  obtain ⟨φ, hφ⟩ := exists_coord_of (Formalism.L2.DIV.oToS D.host.F D.host.E) l.prod l.coprime
    (resI D.host.F l.Mb (half_ne_bot l)) (resI_oToS _ _) (resI_eq_zero_iff _ _) ρ hlin hsur (hker _ _ l.prod)
  refine ⟨φ, fun κ h a ha a' ha' => ?_⟩
  have h1 := hcong κ _ (Formalism.L2.DIV.frGL_pullFr β ⟨_, h⟩).symm a a'
  have h2 := hφ (Formalism.L2.DIV.pullFr β ⟨_, h⟩).1 a ha a' ha'
  have h3 := h1.trans h2
  exact h3

end Dict

end GlobalTheory.GeoActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField

namespace GlobalTheory.WeilSchrodinger

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def sesq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) :
    (Fin k → D.host.E) →ₗ⋆[D.host.E] (Fin k → D.host.E) →ₗ[D.host.E] D.host.E :=
  Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) G

def hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm) (nd : (sesq D G).Nondegenerate)
    (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D where
  V := Fin k → D.host.E
  hT := sesq D G
  herm := herm
  nondeg := nd
  rank := k
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := sg
  L0 := L
  standardTuple_isLattice := hL
  baseLattice_isUnimodular := hU

variable {D}

theorem gram_hspOf {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (herm : (sesq D G).IsSymm)
    (nd : (sesq D G).Nondegenerate) (L : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (hL : L.IsLattice D.host.E)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (sesq D G) L) (sg : (D.host.E →+* ℂ) → ℕ × ℕ) :
    (hspOf D G herm nd L hL hU sg).gram = G := by
  funext i j
  have e : ∀ m : Fin k, Pi.basisFun D.host.E (Fin k) m = Pi.single m 1 := fun m => Pi.basisFun_apply _ _ m
  simp only [HSpace.gram, hspOf, sesq]
  erw [e i, e j]
  exact Matrix.toLinearMapₛₗ₂'_single (R := D.host.E) (starRingEnd D.host.E) (RingHom.id D.host.E) G i j

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFinitenessAutomorphicGLOfEigenStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_finiteness_automorphic_GL_of_eigen : GlobalTheory.HCF.CoreFiniteGL → GlobalTheory.Published.AutomorphicFormsFiniteGL := by
  first | exact @GlobalTheory.HCF.automorphicFormsFiniteGL_of_core | exact GlobalTheory.HCF.automorphicFormsFiniteGL_of_core | (intros; apply GlobalTheory.HCF.automorphicFormsFiniteGL_of_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSchrodingerLinePureTensorZero
section
namespace SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SchrLine

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x : InfiniteAdeleRing F =>
      ((fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [h]
  exact Continuous.prodMk
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1))
    (continuous_pi fun v =>
      (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
        (continuous_apply v.1))

def arch : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem arch_apply (x : AF F) : arch x = InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := rfl

theorem continuous_arch : Continuous (arch : AF F → mixedEmbedding.mixedSpace F) := by
  have h : (arch : AF F → mixedEmbedding.mixedSpace F) =
      fun x => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 := funext fun x => arch_apply x
  rw [h]
  exact continuous_toMixed.comp continuous_fst

def coord (hF : IsTotallyReal F) (w : InfinitePlace F) : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (⟨w, hF.isReal w⟩ : {w : InfinitePlace F // w.IsReal})).comp
    (ContinuousLinearMap.fst ℝ _ _)

theorem re_eq_coord (hF : IsTotallyReal F) (x : Ainf F) (w : InfinitePlace F) :
    re x w = coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  have h1 : re x w = (InfinitePlace.Completion.extensionEmbedding w (x w)).re := rfl
  have h2 : coord hF w (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w) (x w) := rfl
  rw [h1, h2, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (hF.isReal w), Complex.ofReal_re]

theorem arch_line {M : ℝ →+ VA F N} (hM : IsRealLine M) (p : VA F N →+ AF F) (hp : Continuous p) (s : ℝ) :
    arch (p (M s)) = s • arch (p (M 1)) := by
  let f : ℝ →+ mixedEmbedding.mixedSpace F := ((arch (F := F)).toAddMonoidHom).comp (p.comp M)
  have hf : Continuous f := continuous_arch.comp (hp.comp hM.1)
  have h := map_real_smul f hf s 1
  rw [smul_eq_mul, mul_one] at h
  exact h

theorem arch_fst {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).1 l) = s • arch ((M 1).1 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.fst _ _))
    (by show Continuous (fun u : VA F N => u.1 l); exact (continuous_apply l).comp continuous_fst) s

theorem arch_snd {M : ℝ →+ VA F N} (hM : IsRealLine M) (l : Fin N) (s : ℝ) :
    arch ((M s).2 l) = s • arch ((M 1).2 l) :=
  arch_line hM ((Pi.evalAddMonoidHom (fun _ : Fin N => AF F) l).comp (AddMonoidHom.snd _ _))
    (by show Continuous (fun u : VA F N => u.2 l); exact (continuous_apply l).comp continuous_snd) s

def phaseForm (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ) (B : Fin N → mixedEmbedding.mixedSpace F) :
    (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  ∑ w, ∑ l, (lam w * coord hF w (B l)) • (coord hF w).comp (ContinuousLinearMap.proj l)

theorem phaseForm_apply (hF : IsTotallyReal F) (lam : InfinitePlace F → ℝ)
    (B q : Fin N → mixedEmbedding.mixedSpace F) :
    phaseForm hF lam B q = ∑ w, lam w * ∑ l, coord hF w (q l) * coord hF w (B l) := by
  simp only [phaseForm, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem re_fstA_eq_coord_arch (hF : IsTotallyReal F) (u : AF F) (w : InfinitePlace F) :
    re (fstA F u) w = coord hF w (arch u) := by
  first | (rw [re_eq_coord hF, arch_apply]; rfl) | rw [re_eq_coord hF, arch_apply]

theorem phase_line [Invertible (2 : AF F)] (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ}
    {lam : InfinitePlace F → ℝ} (hlam : IsLam ψ lam) {M : ℝ →+ VA F N} (hM : IsRealLine M)
    (z : Fin N → AF F) (s : ℝ) :
    ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
          s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
            ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) : ℝ) : ℂ)) := by
  haveI : IsTotallyReal F := hF
  have hy0 : ∀ l, sndA F ((M s).2 l) = 0 := fun l => congrFun (hM.2 s).2 l
  have hsnd : sndA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_mul, map_sum, hy0, mul_zero, Finset.sum_const_zero, add_zero]
  have e1 : ∀ w, re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) +
        s ^ 2 * (coord hF w (arch ⅟(2 : AF F)) *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    intro w
    have hxs : ∀ l, arch ((M s).1 l) = s • arch ((M 1).1 l) := fun l => arch_fst hM l s
    have hys : ∀ l, arch ((M s).2 l) = s • arch ((M 1).2 l) := fun l => arch_snd hM l s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_mul, map_sum, re_add, re_mul, re_sum, re_fstA_eq_coord_arch hF, hxs, hys,
      map_smul, smul_eq_mul]
    first
      | (simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
         refine Finset.sum_congr rfl fun l _ => ?_
         ring)
      | (have h1 : ∑ l, coord hF w (arch (z l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s * ∑ l, coord hF w (arch (z l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         have h2 : ∑ l, s * coord hF w (arch ((M 1).1 l)) * (s * coord hF w (arch ((M 1).2 l))) =
            s ^ 2 * ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l)) := by
           rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
         rw [h1, h2]
         ring)
  have key : ∑ w, lam w * re (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) w =
      s * phaseForm hF lam (fun l => arch ((M 1).2 l)) (fun l => arch (z l)) +
        s ^ 2 * ∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w *
          ∑ l, coord hF w (arch ((M 1).1 l)) * coord hF w (arch ((M 1).2 l))) := by
    have hms : ∀ (c : ℝ) (h : InfinitePlace F → ℝ), c * ∑ w, h w = ∑ w, c * h w :=
      fun c h => Finset.mul_sum _ _ _
    rw [phaseForm_apply, hms s, hms (s ^ 2), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [e1, re_fstA_eq_coord_arch hF]
    ring
  calc ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))
      = ψ (pairA F (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2))) 0) := by
        first | (rw [← hsnd]; rfl) | rw [← hsnd]
    _ = _ := by
        have h2 := hlam.2 (fstA F (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)))
        rw [key] at h2
        exact h2

private theorem hasDerivAt_exp_quadratic_mul_schwartz_line_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (q v : E) (a b : ℝ) (c : ℂ) :
    HasDerivAt (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((s * a + s ^ 2 * b : ℝ) : ℂ)) *
        (f (q + s • v) * c))
      ((2 * Real.pi * Complex.I * a * f q + fderiv ℝ f q v) * c) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s * a + s ^ 2 * b) a 0 := by
    have h := ((hasDerivAt_id' (0:ℝ)).mul_const a).add (((hasDerivAt_id' (0:ℝ)).pow 2).mul_const b)
    first
      | exact h.congr_deriv (by simp)
      | (convert h using 1 <;> simp)
  have h3 := (h1.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have hl : HasDerivAt (fun s : ℝ => q + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add q
  have hf0 : HasFDerivAt (⇑f) (fderiv ℝ f q) (q + (0:ℝ) • v) := by
    rw [zero_smul, add_zero]
    exact f.hasFDerivAt q
  have h4 := (hf0.comp_hasDerivAt (0:ℝ) hl).mul_const c
  have h5 := h3.mul h4
  convert h5 using 1
  all_goals first
    | rfl
    | (simp only [Function.comp_apply]; done)
    | (simp; done)
    | (simp; ring)
    | (funext s; simp [Function.comp_apply])

end GlobalTheory.CompanionTheory.SchrLine


open GlobalTheory.CompanionTheory.SchrLine in
theorem GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA :
    ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F →
    IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M →
    ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) →
    ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F,
      HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 := by
  intro F _ _ N _ ψ hF hψ M hM f g hg
  obtain ⟨lam, hlam⟩ := GlobalTheory.SWQ.exists_isLam F hF ψ hψ
  let L : (Fin N → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) •
      (Complex.ofRealCLM.comp (phaseForm hF lam (fun l => arch ((M 1).2 l))))
  let v : Fin N → mixedEmbedding.mixedSpace F := fun l => arch ((M 1).1 l)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f, fun z => ?_⟩
  let q : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : Fin N → FiniteAdeleRing (𝓞 F) F := fun i => (z i).2
  have hfun : ∀ s : ℝ, GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z =
      Complex.exp (2 * Real.pi * Complex.I * ((s * GlobalTheory.CompanionTheory.SchrLine.phaseForm hF lam (fun l => GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)) (fun l => GlobalTheory.CompanionTheory.SchrLine.arch (z l)) + s ^ 2 * (∑ w, lam w * (re (fstA F ⅟(2 : AF F)) w * ∑ l, GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).1 l)) * GlobalTheory.CompanionTheory.SchrLine.coord hF w (GlobalTheory.CompanionTheory.SchrLine.arch ((M 1).2 l)))) : ℝ) : ℂ)) *
        (f (q + s • v) * g zf) := by
    intro s
    have hq : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) = q + s • v := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (z i + (M s).1 i)) = q i + s • v i
      rw [map_add (f := _), map_add (f := _)]
      first
        | exact congrArg₂ (· + ·) rfl (arch_fst hM i s)
        | (congr 1; exact arch_fst hM i s)
    have hz : (fun i => ((z + (M s).1) i).2) = zf := by
      funext i
      show sndA F (z i + (M s).1 i) = (z i).2
      rw [map_add (f := _), show sndA F ((M s).1 i) = 0 from congrFun (hM.2 s).1 i]
      exact add_zero _
    show ψ (z ⬝ᵥ (M s).2 + ⅟(2 : AF F) * ((M s).1 ⬝ᵥ (M s).2)) *
        (f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + (M s).1) i).1) *
          g (fun i => ((z + (M s).1) i).2)) = _
    rw [phase_line hF hlam hM z s, hq, hz]
  rw [show (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) = _ from funext hfun]
  refine (hasDerivAt_exp_quadratic_mul_schwartz_line_zero f q v _ _ (g zf)).congr_deriv ?_
  show _ = (SchwartzMap.smulLeftCLM ℂ (⇑L) f + LineDeriv.lineDerivOp v f) q * g zf
  rw [SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply L.hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  first
    | rfl
    | (simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        Complex.ofRealCLM_apply, smul_eq_mul]; rfl)
    | (simp [L, smul_eq_mul]; ring)

end
end

end SchrodingerLinePhase
section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical
theorem _root_.GlobalTheory.Adopt.hasDerivAt_schrodingerLine_pureTensor_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (Fin N → FiniteAdeleRing (𝓞 F) F) → ∃ f' : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ z : Fin N → AF F, HasDerivAt (fun s : ℝ => GlobalTheory.WeilM.schr ψ (M s) (GlobalTheory.WeilM.pureA F f g) z) (GlobalTheory.WeilM.pureA F f' g z) 0 :=
  SchrodingerLinePhase.GlobalTheory.CompanionTheory.SchrLine.exists_hasDerivAt_schr_pureA

end
end

