module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieDim

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.FrobeniusOrbits

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def tieIw {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) (v : Fin G.P.nV) : E →+* G.P.Qq v :=
  ((t.eQ v _ rfl).symm : (t.pl v).1.adicCompletion F →+* G.P.Qq v).comp
    (((RingHom.fst _ _).comp (t.spl _ (t.pl v).2).toRingHom).comp (inclE (F := F) ((t.pl v).1.adicCompletion F)))

theorem tieIw_levTieOf {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    tieIw (levTieOf h t) = tieIw t := by
  subst h
  rfl

end Cast

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 4000000 in
theorem locAt_iw_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w)))))
    (x : D.host.E) :
    (Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x = (I u w hg).iw v x := by
  show tieIw ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) v x = _
  simp only [hermitianLevelZeroOfRecursion]
  erw [tieIw_levTieOf]
  rfl


set_option maxHeartbeats 4000000 in
theorem pos_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
    (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
      (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
    (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
      lamV (lam u w hg) (D.what₂.embLL z))
    (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))) (s : Fin (nFr D (D.what₂.places.resChar w))) (x : D.host.E) :
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (Cmp.tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
      ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((Cmp.locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x)) := by
  rw [locAt_iw_C D sc Ce Lc I ψ hd H0 hL B u w hg v x]
  apply (iK u w hg).injective
  have h1 := hK u w hg (Cmp.tEL D (D.eTau.symm (posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩))
    (if Even s.val then x else sigD D x))
  have h2 := hPos u w hg v s x
  have h3 : sigD D x = D.host.conj x := bridge_star_holds D.R D.host x
  have h4 : D.what₂.embLL (Cmp.tEL D (D.eTau.symm (posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩))
      (if Even s.val then x else sigD D x)) =
      D.host.emb (((posG (zPsi D.R.toFrame (D.R.iota (hP D (D.what₂.places.resChar w)))) ⟨v, s⟩ : D.R.Psi) : D.R.GG) *
        D.R.cc ^ s.val) x := by
    rw [Cmp.tEL_emb, emb_conj_pow]
    unfold embT
    rw [Equiv.apply_symm_apply, h3]
    congr 1
    by_cases hs : s.val % 2 = 1
    · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
      simp [hs, this]
    · have : Even s.val := by rw [Nat.even_iff]; omega
      simp [hs, this]
  rw [h4] at h1
  exact h1.trans h2.symm

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsiC
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem levTieOf_yG {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).yG = t.yG := by
  subst h
  rfl

theorem levTieOf_gamI {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).gamI = t.gamI := by
  subst h
  rfl

theorem gamToUp_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
    (σE : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) (Up : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : gamC σE J Up y) :
    (gamToUp σE J Up y γ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ) * y := by
  show (MulAut.conj y⁻¹) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ)) = _
  rw [MulAut.conj_apply, inv_inv]

end Cast

def ChiClause {D : D7} {X : Formalism.L2.Herm.Herm0 D} (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : Prop :=
  ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 8000000 in
theorem chi_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    ChiClause T (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) := by
  intro u w hg i γ κ hκ
  refine chi_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u w hg B _ (Lc u) (hL u) (ψ u w hg) ?_ (hψ u w hg) i γ κ hκ
  intro i γ a ha
  have e1 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).yG = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).yG :=
    levTieOf_yG (hL u) _
  have e2 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).gamI = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).gamI :=
    levTieOf_gamI (hL u) _
  rw [e1, e2] at ha
  have e3 : a = gamToUp D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w))
      (repP (Lc u) (D.what₂.places.resChar w) i : GL (Fin D.R.k) _) γ :=
    Subtype.ext (ha.trans (gamToUp_val _ _ _ _ γ).symm)
  rw [e3]
  rfl

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtC
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section C

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)


set_option maxHeartbeats 4000000 in
theorem hypT_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    HypT ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) :=
  hypT_of (hL u) _ (I u w hg) (levTieOf_fr (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg))
    (levTieOf_spl (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg)) (isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))

end C

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieSurj
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}
  {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem card_eq_d (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Fintype.card ((D.fm u).lat 0).ι = Module.finrank (D.gat u w hg).O (D.gat u w hg).M := by
  have h1 : Module.finrank ℂ ((D.fm u).Fi 0) = Fintype.card ((D.fm u).lat 0).ι := by
    rw [← ((D.fm u).emb_basis 0).2]
    exact finrank_span_eq_card ((D.fm u).emb_basis 0).1
  have h2 : Module.finrank ℂ ((D.fm u).Fi 0) = Module.finrank ℂ (D.mem u).A.Mu0 :=
    congrArg (fun S : Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) => Module.finrank ℂ S) (D.fm u).Fi_zero
  exact h1.symm.trans (h2.trans (D.gat_d u w hg).symm)

def cmpLin (H : CmpCore T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V →ₛₗ[I.embW u w hg] (D.gat u w hg).Fn :=
  cmpL (e := I.embW u w hg) (H.ex u w hg) (valUniq_of (embT_conj D) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B))

theorem cmpLin_mem_span (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : ((D.fm u).lat 0).V) :
    cmpLin H u w hg x ∈ Submodule.span (D.gat u w hg).Kf ((D.gat u w hg).M : Set (D.gat u w hg).Fn) := by
  have hx : x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    apply Submodule.subset_span
    exact (cmpRec_lat_pf H hloc u w hg y).2 (Submodule.subset_span hy)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h1 => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ h1


set_option maxHeartbeats 1000000 in
theorem surjRat_pf (H : CmpCore T Gt I) (hloc : ValIntRec T Gt I)
    (hfrac : ∀ u w hg, IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hfin : ∀ u w hg, Module.Finite (D.gat u w hg).O (D.gat u w hg).M) : SurjRat T Gt I := by
  intro u w hg F hF hrat
  have := hfrac u w hg
  have := hfin u w hg
  have hli : LinearIndependent (D.gat u w hg).Kf fun a => cmpLin H u w hg (((D.fm u).lat 0).b a) :=
    cmpC_li (e := I.embW u w hg) (embT_conj D) (H.ex u w hg)
      (valUniq_of (embT_conj D) (evInj_rec Gt I u w hg) (ptEx_rec X T u w hg I.B)) (ptAll_rec X T u (H.same u) w hg I.B)
      (embFr_inj T u) ((D.fm u).lat 0).b ((D.fm u).lat 0).b.linearIndependent
  have h1 : F ∈ Submodule.span (D.gat u w hg).Kf (Set.range fun a => cmpLin H u w hg (((D.fm u).lat 0).b a)) :=
    mem_span_of_card (D.gat u w hg).M _ hli (fun a => cmpLin_mem_span H hloc u w hg _) (card_eq_d D u w hg) F hF
  have h2 : F ∈ Submodule.span (D.gat u w hg).Kf (Set.range (cmpLin H u w hg).toAddMonoidHom) := by
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  exact rat_mem (I.embW u w hg) (evG (D.gat u w hg)) (cmpLin H u w hg).toAddMonoidHom (evG_sep _)
    (fun a x => (cmpLin H u w hg).map_smulₛₗ a x) (fun x => (ratFn_iff _ _ _).1 (cmpC_rat x)) h2
    ((ratFn_iff _ _ _).1 hrat)

end Formalism.L2.G
end
end

