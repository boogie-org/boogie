(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@Value 0)
(declare-sort T@Loc_5601 0)
(declare-datatypes ((T@Vec_2306 0)) (((Vec_2306 (|contents#Vec_2306| (Array Int Int)) (|len#Vec_2306| Int) ) ) ))
(declare-datatypes ((T@Vec_5 0)) (((Vec_5 (|contents#Vec_5| (Array Int Bool)) (|len#Vec_5| Int) ) ) ))
(declare-datatypes ((T@One_7133 0)) (((One_7133 (|val#One_7133| T@Loc_5601) ) ) ))
(declare-datatypes ((T@Set_35 0)) (((Set_35 (|val#Set_35| (Array Int Bool)) ) ) ))
(declare-datatypes ((T@ChannelOp 0)) (((Send ) (Receive ) ) ))
(declare-datatypes ((T@Set_5604 0)) (((Set_5604 (|val#Set_5604| (Array T@ChannelOp Bool)) ) ) ))
(declare-datatypes ((T@Fraction_5603_5604 0)) (((Fraction_5603_5604 (|val#Fraction_5603_5604| T@Loc_5601) (|id#Fraction_5603_5604| T@ChannelOp) (|ids#Fraction_5603_5604| T@Set_5604) ) ) ))
(declare-datatypes ((T@One_6299 0)) (((One_6299 (|val#One_6299| T@Fraction_5603_5604) ) ) ))
(declare-datatypes ((T@Set_6023 0)) (((Set_6023 (|val#Set_6023| (Array T@Fraction_5603_5604 Bool)) ) ) ))
(declare-datatypes ((T@Fraction_5648_35 0)) (((Fraction_5648_35 (|val#Fraction_5648_35| T@Fraction_5603_5604) (|id#Fraction_5648_35| Int) (|ids#Fraction_5648_35| T@Set_35) ) ) ))
(declare-datatypes ((T@One_8419 0)) (((One_8419 (|val#One_8419| T@Fraction_5648_35) ) ) ))
(declare-datatypes ((T@Set_5987 0)) (((Set_5987 (|val#Set_5987| (Array T@Fraction_5648_35 Bool)) ) ) ))
(declare-datatypes ((T@read_s 0)) (((read_s (|s#read_s| T@Fraction_5603_5604) (|perm#read_s| T@One_8419) ) ) ))
(declare-datatypes ((T@Choice_Inv_s 0)) (((Choice_Inv_s_read_s (|read_s#Choice_Inv_s_read_s| T@read_s) ) ) ))
(declare-datatypes ((|T@main_s'| 0)) (((|main_s'| (|send#main_s'| T@Fraction_5603_5604) (|sps#main_s'| T@Set_5987) ) ) ))
(declare-datatypes ((T@action_main_s 0)) (((action_main_s (|send#action_main_s| T@Fraction_5603_5604) (|sps#action_main_s| T@Set_5987) ) ) ))
(declare-datatypes ((T@read_f 0)) (((read_f (|s#read_f| T@Fraction_5603_5604) (|perm#read_f| T@One_8419) ) ) ))
(declare-datatypes ((T@Choice_Inv_f 0)) (((Choice_Inv_f_read_f (|read_f#Choice_Inv_f_read_f| T@read_f) ) ) ))
(declare-datatypes ((|T@main_f'| 0)) (((|main_f'| (|send#main_f'| T@Fraction_5603_5604) (|sps#main_f'| T@Set_5987) ) ) ))
(declare-datatypes ((T@action_main_f 0)) (((action_main_f (|send#action_main_f| T@Fraction_5603_5604) (|sps#action_main_f| T@Set_5987) ) ) ))
(declare-datatypes ((T@StampedValue 0)) (((StampedValue (|ts#StampedValue| Int) (|value#StampedValue| T@Value) ) ) ))
(declare-datatypes ((T@Cell_6356_6358 0)) (((Cell_6356_6358 (|key#Cell_6356_6358| T@Fraction_5603_5604) (|val#Cell_6356_6358| (Array Int T@StampedValue)) ) ) ))
(declare-datatypes ((T@Map_6023_6025 0)) (((Map_6023_6025 (|dom#Map_6023_6025| T@Set_6023) (|val#Map_6023_6025| (Array T@Fraction_5603_5604 (Array Int T@StampedValue))) ) ) ))
(declare-fun Set_Size_6023 (T@Set_6023) Int)
(declare-fun Set_Size_5987 (T@Set_5987) Int)
(declare-fun Set_Size_35 (T@Set_35) Int)
(declare-fun Set_Size_5604 (T@Set_5604) Int)
(declare-fun |lambda#8| (T@Fraction_5603_5604 Int Int T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun |lambda#1| (Int Int) (Array Int Bool))
(declare-fun |lambda#0| (T@Fraction_5603_5604 T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun Identity () (Array Int Int))
(declare-fun |lambda#9| (T@Fraction_5603_5604 Int Int T@Fraction_5603_5604 T@Set_35) (Array T@read_f Bool))
(declare-fun |lambda#33| (T@Fraction_5603_5604 Int Int T@Fraction_5603_5604 T@Set_35) (Array T@read_s Bool))
(declare-fun Default_2306 () Int)
(declare-fun Default_5 () Bool)
(declare-fun |lambda#2| (T@Loc_5601 T@Set_5604 T@Set_5604) (Array T@Fraction_5603_5604 Bool))
(declare-fun |lambda#3| (T@Fraction_5603_5604 T@Set_35 T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun |lambda#53| (T@Fraction_5603_5604 T@Set_5987) (Array T@read_f Bool))
(declare-fun |lambda#55| (T@Fraction_5603_5604 T@Set_5987) (Array T@read_s Bool))
(declare-fun Choice_6023 ((Array T@Fraction_5603_5604 Bool)) T@Fraction_5603_5604)
(declare-fun Choice_2289 ((Array Int Bool)) Int)
(declare-fun Choice_9763 ((Array T@Fraction_5648_35 Bool)) T@Fraction_5648_35)
(declare-fun Choice_4318 ((Array T@ChannelOp Bool)) T@ChannelOp)
(declare-fun n () Int)
(assert (forall ((a T@Set_6023) (t T@Fraction_5603_5604) ) (! (= (Set_Size_6023 (Set_6023 (store (|val#Set_6023| a) t false))) (ite (select (|val#Set_6023| a) t) (- (Set_Size_6023 a) 1) (Set_Size_6023 a)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_6023 (store (|val#Set_6023| a) t false)))
)))
(assert (forall ((a@@0 T@Set_5987) (t@@0 T@Fraction_5648_35) ) (! (= (Set_Size_5987 (Set_5987 (store (|val#Set_5987| a@@0) t@@0 false))) (ite (select (|val#Set_5987| a@@0) t@@0) (- (Set_Size_5987 a@@0) 1) (Set_Size_5987 a@@0)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_5987 (store (|val#Set_5987| a@@0) t@@0 false)))
)))
(assert (forall ((a@@1 T@Set_35) (t@@1 Int) ) (! (= (Set_Size_35 (Set_35 (store (|val#Set_35| a@@1) t@@1 false))) (ite (select (|val#Set_35| a@@1) t@@1) (- (Set_Size_35 a@@1) 1) (Set_Size_35 a@@1)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_35 (store (|val#Set_35| a@@1) t@@1 false)))
)))
(assert (forall ((a@@2 T@Set_5604) (t@@2 T@ChannelOp) ) (! (= (Set_Size_5604 (Set_5604 (store (|val#Set_5604| a@@2) t@@2 false))) (ite (select (|val#Set_5604| a@@2) t@@2) (- (Set_Size_5604 a@@2) 1) (Set_Size_5604 a@@2)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_5604 (store (|val#Set_5604| a@@2) t@@2 false)))
)))
(assert (forall ((x T@Vec_2306) ) (! (>= (|len#Vec_2306| x) 0)
 :qid |basebpl.75:32|
 :skolemid |6|
 :pattern ( (|len#Vec_2306| x))
)))
(assert (forall ((x@@0 T@Vec_5) ) (! (>= (|len#Vec_5| x@@0) 0)
 :qid |basebpl.75:32|
 :skolemid |6|
 :pattern ( (|len#Vec_5| x@@0))
)))
(assert (forall ((|l#0| T@Fraction_5603_5604) (|l#1| Int) (|l#2| Int) (|l#3| T@Set_35) (x@@1 T@Fraction_5648_35) ) (! (= (select (|lambda#8| |l#0| |l#1| |l#2| |l#3|) x@@1)  (and (and (and (= (|val#Fraction_5648_35| x@@1) |l#0|) (<= |l#1| (|id#Fraction_5648_35| x@@1))) (<= (|id#Fraction_5648_35| x@@1) |l#2|)) (= (|ids#Fraction_5648_35| x@@1) |l#3|)))
 :qid |snapshotscattergatherbpl.201:25|
 :skolemid |339|
 :pattern ( (select (|lambda#8| |l#0| |l#1| |l#2| |l#3|) x@@1))
)))
(assert (= (Set_Size_6023 (Set_6023 ((as const (Array T@Fraction_5603_5604 Bool)) false))) 0))
(assert (= (Set_Size_5987 (Set_5987 ((as const (Array T@Fraction_5648_35 Bool)) false))) 0))
(assert (= (Set_Size_35 (Set_35 ((as const (Array Int Bool)) false))) 0))
(assert (= (Set_Size_5604 (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) 0))
(assert (forall ((a@@3 T@Set_6023) (b T@Set_6023) ) (! (= (+ (Set_Size_6023 (Set_6023 ((_ map or) (|val#Set_6023| a@@3) (|val#Set_6023| b)))) (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@3) (|val#Set_6023| b))))) (+ (Set_Size_6023 a@@3) (Set_Size_6023 b)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_6023 ((_ map or) (|val#Set_6023| a@@3) (|val#Set_6023| b))))
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@3) (|val#Set_6023| b))))
)))
(assert (forall ((a@@4 T@Set_5987) (b@@0 T@Set_5987) ) (! (= (+ (Set_Size_5987 (Set_5987 ((_ map or) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0)))) (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))) (+ (Set_Size_5987 a@@4) (Set_Size_5987 b@@0)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_5987 ((_ map or) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))
)))
(assert (forall ((a@@5 T@Set_35) (b@@1 T@Set_35) ) (! (= (+ (Set_Size_35 (Set_35 ((_ map or) (|val#Set_35| a@@5) (|val#Set_35| b@@1)))) (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))) (+ (Set_Size_35 a@@5) (Set_Size_35 b@@1)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_35 ((_ map or) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))
)))
(assert (forall ((a@@6 T@Set_5604) (b@@2 T@Set_5604) ) (! (= (+ (Set_Size_5604 (Set_5604 ((_ map or) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2)))) (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))) (+ (Set_Size_5604 a@@6) (Set_Size_5604 b@@2)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_5604 ((_ map or) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (x@@2 Int) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0|) x@@2)  (and (<= |l#0@@0| x@@2) (<= x@@2 |l#1@@0|)))
 :qid |snapshotscattergatherbpl.61:40|
 :skolemid |336|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0|) x@@2))
)))
(assert (forall ((a@@7 T@Set_6023) (t@@3 T@Fraction_5603_5604) ) (! (= (Set_Size_6023 (Set_6023 (store (|val#Set_6023| a@@7) t@@3 true))) (ite (select (|val#Set_6023| a@@7) t@@3) (Set_Size_6023 a@@7) (+ (Set_Size_6023 a@@7) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_6023 (store (|val#Set_6023| a@@7) t@@3 true)))
)))
(assert (forall ((a@@8 T@Set_5987) (t@@4 T@Fraction_5648_35) ) (! (= (Set_Size_5987 (Set_5987 (store (|val#Set_5987| a@@8) t@@4 true))) (ite (select (|val#Set_5987| a@@8) t@@4) (Set_Size_5987 a@@8) (+ (Set_Size_5987 a@@8) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_5987 (store (|val#Set_5987| a@@8) t@@4 true)))
)))
(assert (forall ((a@@9 T@Set_35) (t@@5 Int) ) (! (= (Set_Size_35 (Set_35 (store (|val#Set_35| a@@9) t@@5 true))) (ite (select (|val#Set_35| a@@9) t@@5) (Set_Size_35 a@@9) (+ (Set_Size_35 a@@9) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_35 (store (|val#Set_35| a@@9) t@@5 true)))
)))
(assert (forall ((a@@10 T@Set_5604) (t@@6 T@ChannelOp) ) (! (= (Set_Size_5604 (Set_5604 (store (|val#Set_5604| a@@10) t@@6 true))) (ite (select (|val#Set_5604| a@@10) t@@6) (Set_Size_5604 a@@10) (+ (Set_Size_5604 a@@10) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_5604 (store (|val#Set_5604| a@@10) t@@6 true)))
)))
(assert (forall ((|l#0@@1| T@Fraction_5603_5604) (|l#1@@1| T@Set_35) (x@@3 T@Fraction_5648_35) ) (! (= (select (|lambda#0| |l#0@@1| |l#1@@1|) x@@3)  (and (and (= (|val#Fraction_5648_35| x@@3) |l#0@@1|) (= (|ids#Fraction_5648_35| x@@3) |l#1@@1|)) (select (|val#Set_35| (|ids#Fraction_5648_35| x@@3)) (|id#Fraction_5648_35| x@@3))))
 :qid |snapshotscattergatherbpl.55:38|
 :skolemid |335|
 :pattern ( (select (|lambda#0| |l#0@@1| |l#1@@1|) x@@3))
)))
(assert (forall ((a@@11 T@Set_6023) (b@@3 T@Set_6023) ) (! (= (Set_Size_6023 a@@11) (+ (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@11) ((_ map not) (|val#Set_6023| b@@3))))) (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@11) ((_ map not) (|val#Set_6023| b@@3)))))
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))
 :pattern ( (Set_6023 ((_ map or) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))
)))
(assert (forall ((a@@12 T@Set_5987) (b@@4 T@Set_5987) ) (! (= (Set_Size_5987 a@@12) (+ (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@12) ((_ map not) (|val#Set_5987| b@@4))))) (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@12) ((_ map not) (|val#Set_5987| b@@4)))))
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))
 :pattern ( (Set_5987 ((_ map or) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))
)))
(assert (forall ((a@@13 T@Set_35) (b@@5 T@Set_35) ) (! (= (Set_Size_35 a@@13) (+ (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@13) ((_ map not) (|val#Set_35| b@@5))))) (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@13) ((_ map not) (|val#Set_35| b@@5)))))
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))
 :pattern ( (Set_35 ((_ map or) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))
)))
(assert (forall ((a@@14 T@Set_5604) (b@@6 T@Set_5604) ) (! (= (Set_Size_5604 a@@14) (+ (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@14) ((_ map not) (|val#Set_5604| b@@6))))) (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@14) ((_ map not) (|val#Set_5604| b@@6)))))
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))
 :pattern ( (Set_5604 ((_ map or) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))
)))
(assert (forall ((x@@4 Int) ) (! (= (select Identity x@@4) x@@4)
 :qid |basebpl.64:15|
 :skolemid |4|
)))
(assert (forall ((|l#0@@2| T@Fraction_5603_5604) (|l#1@@2| Int) (|l#2@@0| Int) (|l#3@@0| T@Fraction_5603_5604) (|l#4| T@Set_35) (pa T@read_f) ) (! (= (select (|lambda#9| |l#0@@2| |l#1@@2| |l#2@@0| |l#3@@0| |l#4|) pa)  (and (and (and (and (= (|s#read_f| pa) |l#0@@2|) (<= |l#1@@2| (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))))) (<= (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#2@@0|)) (= (|val#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#3@@0|)) (= (|ids#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#4|)))
 :qid |snapshotscattergatherbpl.201:25|
 :skolemid |340|
 :pattern ( (select (|lambda#9| |l#0@@2| |l#1@@2| |l#2@@0| |l#3@@0| |l#4|) pa))
)))
(assert (forall ((|l#0@@3| T@Fraction_5603_5604) (|l#1@@3| Int) (|l#2@@1| Int) (|l#3@@1| T@Fraction_5603_5604) (|l#4@@0| T@Set_35) (pa@@0 T@read_s) ) (! (= (select (|lambda#33| |l#0@@3| |l#1@@3| |l#2@@1| |l#3@@1| |l#4@@0|) pa@@0)  (and (and (and (and (= (|s#read_s| pa@@0) |l#0@@3|) (<= |l#1@@3| (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))))) (<= (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#2@@1|)) (= (|val#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#3@@1|)) (= (|ids#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#4@@0|)))
 :qid |snapshotscattergatherbpl.299:25|
 :skolemid |341|
 :pattern ( (select (|lambda#33| |l#0@@3| |l#1@@3| |l#2@@1| |l#3@@1| |l#4@@0|) pa@@0))
)))
(assert (forall ((x@@5 T@Vec_2306) ) (! (= ((_ map (ite (Bool Int Int) Int)) ((_ map and) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) 0) Identity) ((_ map not) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) (+ 0 (|len#Vec_2306| x@@5))) Identity))) ((as const (Array Int Int)) Default_2306) (|contents#Vec_2306| x@@5)) ((as const (Array Int Int)) Default_2306))
 :qid |basebpl.74:32|
 :skolemid |5|
 :pattern ( (|len#Vec_2306| x@@5))
 :pattern ( (|contents#Vec_2306| x@@5))
)))
(assert (forall ((x@@6 T@Vec_5) ) (! (= ((_ map (ite (Bool Bool Bool) Bool)) ((_ map and) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) 0) Identity) ((_ map not) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) (+ 0 (|len#Vec_5| x@@6))) Identity))) ((as const (Array Int Bool)) Default_5) (|contents#Vec_5| x@@6)) ((as const (Array Int Bool)) Default_5))
 :qid |basebpl.74:32|
 :skolemid |5|
 :pattern ( (|len#Vec_5| x@@6))
 :pattern ( (|contents#Vec_5| x@@6))
)))
(assert (forall ((|l#0@@4| T@Loc_5601) (|l#1@@4| T@Set_5604) (|l#2@@2| T@Set_5604) (piece T@Fraction_5603_5604) ) (! (= (select (|lambda#2| |l#0@@4| |l#1@@4| |l#2@@2|) piece)  (and (and (= (|val#Fraction_5603_5604| piece) |l#0@@4|) (select (|val#Set_5604| |l#1@@4|) (|id#Fraction_5603_5604| piece))) (= (|ids#Fraction_5603_5604| piece) |l#2@@2|)))
 :qid |basebpl.303:67|
 :skolemid |337|
 :pattern ( (select (|lambda#2| |l#0@@4| |l#1@@4| |l#2@@2|) piece))
)))
(assert (forall ((|l#0@@5| T@Fraction_5603_5604) (|l#1@@5| T@Set_35) (|l#2@@3| T@Set_35) (piece@@0 T@Fraction_5648_35) ) (! (= (select (|lambda#3| |l#0@@5| |l#1@@5| |l#2@@3|) piece@@0)  (and (and (= (|val#Fraction_5648_35| piece@@0) |l#0@@5|) (select (|val#Set_35| |l#1@@5|) (|id#Fraction_5648_35| piece@@0))) (= (|ids#Fraction_5648_35| piece@@0) |l#2@@3|)))
 :qid |basebpl.303:67|
 :skolemid |338|
 :pattern ( (select (|lambda#3| |l#0@@5| |l#1@@5| |l#2@@3|) piece@@0))
)))
(assert (forall ((|l#0@@6| T@Fraction_5603_5604) (|l#1@@6| T@Set_5987) (pa@@1 T@read_f) ) (! (= (select (|lambda#53| |l#0@@6| |l#1@@6|) pa@@1)  (and (= (|s#read_f| pa@@1) |l#0@@6|) (select (|val#Set_5987| |l#1@@6|) (|val#One_8419| (|perm#read_f| pa@@1)))))
 :qid |snapshotscattergatherbpl.141:39|
 :skolemid |342|
 :pattern ( (select (|lambda#53| |l#0@@6| |l#1@@6|) pa@@1))
)))
(assert (forall ((|l#0@@7| T@Fraction_5603_5604) (|l#1@@7| T@Set_5987) (pa@@2 T@read_s) ) (! (= (select (|lambda#55| |l#0@@7| |l#1@@7|) pa@@2)  (and (= (|s#read_s| pa@@2) |l#0@@7|) (select (|val#Set_5987| |l#1@@7|) (|val#One_8419| (|perm#read_s| pa@@2)))))
 :qid |snapshotscattergatherbpl.239:39|
 :skolemid |343|
 :pattern ( (select (|lambda#55| |l#0@@7| |l#1@@7|) pa@@2))
)))
(assert (forall ((a@@15 T@Set_6023) ) (!  (or (= a@@15 (Set_6023 ((as const (Array T@Fraction_5603_5604 Bool)) false))) (< 0 (Set_Size_6023 a@@15)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@16 T@Set_5987) ) (!  (or (= a@@16 (Set_5987 ((as const (Array T@Fraction_5648_35 Bool)) false))) (< 0 (Set_Size_5987 a@@16)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@17 T@Set_35) ) (!  (or (= a@@17 (Set_35 ((as const (Array Int Bool)) false))) (< 0 (Set_Size_35 a@@17)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@18 T@Set_5604) ) (!  (or (= a@@18 (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) (< 0 (Set_Size_5604 a@@18)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@19 (Array T@Fraction_5603_5604 Bool)) ) (!  (or (= a@@19 ((as const (Array T@Fraction_5603_5604 Bool)) false)) (select a@@19 (Choice_6023 a@@19)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_6023 a@@19))
)))
(assert (forall ((a@@20 (Array Int Bool)) ) (!  (or (= a@@20 ((as const (Array Int Bool)) false)) (select a@@20 (Choice_2289 a@@20)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_2289 a@@20))
)))
(assert (forall ((a@@21 (Array T@Fraction_5648_35 Bool)) ) (!  (or (= a@@21 ((as const (Array T@Fraction_5648_35 Bool)) false)) (select a@@21 (Choice_9763 a@@21)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_9763 a@@21))
)))
(assert (forall ((a@@22 (Array T@ChannelOp Bool)) ) (!  (or (= a@@22 ((as const (Array T@ChannelOp Bool)) false)) (select a@@22 (Choice_4318 a@@22)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_4318 a@@22))
)))
(assert (>= n 1))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun mem () (Array Int T@StampedValue))
(declare-fun second_perm () T@One_8419)
(declare-fun second_s () T@Fraction_5603_5604)
(declare-fun pSet@2 () T@Set_5987)
(declare-fun snapshots@2 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun snapshots () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun pSet () T@Set_5987)
(declare-fun contents@2 () T@Map_6023_6025)
(declare-fun contents () T@Map_6023_6025)
(declare-fun first_one_s () T@One_6299)
(declare-fun first_snapshot () (Array Int T@StampedValue))
(declare-fun inline$read_s$0$v@0 () T@Value)
(declare-fun inline$read_s$0$k@0 () Int)
(declare-fun pSet@0 () T@Set_5987)
(declare-fun contents@0 () T@Map_6023_6025)
(declare-fun inline$read_s$0$pieces@1 () T@Set_5987)
(declare-fun pSet@1 () T@Set_5987)
(declare-fun inline$read_s$0$one_s@1 () T@One_6299)
(declare-fun inline$read_s$0$inline$Fractions_To_One_9245_198$0$ids@1 () T@Set_35)
(declare-fun inline$read_s$0$inline$Send$0$snapshot@1 () (Array Int T@StampedValue))
(declare-fun inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2 () T@Cell_6356_6358)
(declare-fun contents@1 () T@Map_6023_6025)
(declare-fun snapshots@1 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun snapshots@0 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun Trigger_read_s_v (T@Value) Bool)
(declare-fun Trigger_read_s_k (Int) Bool)
(declare-fun inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2 () T@Cell_6356_6358)
(declare-fun skolemConstant0 () (Array T@Fraction_5648_35 Int))
(declare-fun skolemConstant1 () (Array T@Fraction_5603_5604 Int))
(declare-fun Default_21335 () (Array Int T@StampedValue))
(set-info :boogie-vc-id Civl_CommutativityChecker_Send_read_s)
(set-option :timeout 0)
(set-option :rlimit 0)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(assert (not
 (=> (= (ControlFlow 0 0) 10) (=> true (let ((quantifierBinding1  (or (or (or (and (and (and (and (and (and (and true true) (> (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@2)) ((as const (Array T@Fraction_5648_35 Bool)) true)))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|value#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))))) (= pSet@2 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem)) (and (and (and (and (and (and (and true true) (> (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@2)) ((as const (Array T@Fraction_5648_35 Bool)) true)))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) inline$read_s$0$v@0))))) (= pSet@2 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem))) (and (and (and (and (and (and (and true true) (> inline$read_s$0$k@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@2)) ((as const (Array T@Fraction_5648_35 Bool)) true)))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue inline$read_s$0$k@0 (|value#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))))) (= pSet@2 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem))) (and (and (and (and (and (and (and true true) (> inline$read_s$0$k@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@2)) ((as const (Array T@Fraction_5648_35 Bool)) true)))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue inline$read_s$0$k@0 inline$read_s$0$v@0))))) (= pSet@2 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem)))))
(let ((quantifierBinding0  (or (or (or (and (and (and (and (and (and (and true true) (> (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|value#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))))) (= pSet@2 (Set_5987 ((_ map and) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) ((_ map not) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))))))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem)) (and (and (and (and (and (and (and true true) (> (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))) inline$read_s$0$v@0))))) (= pSet@2 (Set_5987 ((_ map and) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) ((_ map not) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))))))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem))) (and (and (and (and (and (and (and true true) (> inline$read_s$0$k@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue inline$read_s$0$k@0 (|value#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))))) (= pSet@2 (Set_5987 ((_ map and) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) ((_ map not) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))))))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem))) (and (and (and (and (and (and (and true true) (> inline$read_s$0$k@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue inline$read_s$0$k@0 inline$read_s$0$v@0))))) (= pSet@2 (Set_5987 ((_ map and) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) ((_ map not) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))))))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem)))))
(let ((inline$read_s$0$Return_correct  (=> (= (ControlFlow 0 2) (- 0 1)) (=> true (or (or (or quantifierBinding0 quantifierBinding1) (and (and (and (and (and true (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))) (= pSet@2 (Set_5987 ((_ map and) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) ((_ map not) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))))))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| (One_6299 second_s)) (select snapshots@2 (|val#Fraction_5603_5604| second_s))))))) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem))) (and (and (and (and (and true (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@2)) ((as const (Array T@Fraction_5648_35 Bool)) true)))) (= snapshots@2 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))))) (= pSet@2 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) (= contents@2 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)))))) (= mem mem)))))))
(let ((inline$read_s$0$anon6_Else_correct  (=> (and (and (not (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@0)) ((as const (Array T@Fraction_5648_35 Bool)) true))) (= contents@2 contents@0)) (and (= pSet@2 pSet@0) (= (ControlFlow 0 4) 2))) inline$read_s$0$Return_correct)))
(let ((inline$read_s$0$anon6_Then_correct  (=> (and (and (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| pSet@0)) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= inline$read_s$0$pieces@1 (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))))) (and (= pSet@1 (Set_5987 ((_ map and) (|val#Set_5987| pSet@0) ((_ map not) (|val#Set_5987| inline$read_s$0$pieces@1))))) (= inline$read_s$0$one_s@1 (One_6299 second_s)))) (=> (and (and (and (= inline$read_s$0$inline$Fractions_To_One_9245_198$0$ids@1 (Set_35 (|lambda#1| 1 n))) (= inline$read_s$0$inline$Send$0$snapshot@1 (select snapshots@2 (|val#Fraction_5603_5604| second_s)))) (and (= inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2 (Cell_6356_6358 (|val#One_6299| inline$read_s$0$one_s@1) inline$read_s$0$inline$Send$0$snapshot@1)) (not (select (|val#Set_6023| (|dom#Map_6023_6025| contents@0)) (|key#Cell_6356_6358| inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2))))) (and (and (= contents@1 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents@0)) (|key#Cell_6356_6358| inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2) true)) (store (|val#Map_6023_6025| contents@0) (|key#Cell_6356_6358| inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2) (|val#Cell_6356_6358| inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2)))) (= contents@2 contents@1)) (and (= pSet@2 pSet@1) (= (ControlFlow 0 3) 2)))) inline$read_s$0$Return_correct))))
(let ((inline$read_s$0$anon3_correct  (=> (= pSet@0 (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true))) (and (=> (= (ControlFlow 0 5) 3) inline$read_s$0$anon6_Then_correct) (=> (= (ControlFlow 0 5) 4) inline$read_s$0$anon6_Else_correct)))))
(let ((inline$read_s$0$anon5_Else_correct  (=> (= snapshots@1 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm)))))) (=> (and (= snapshots@2 snapshots@1) (= (ControlFlow 0 7) 5)) inline$read_s$0$anon3_correct))))
(let ((inline$read_s$0$anon5_Then_correct  (=> (and (and (> inline$read_s$0$k@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))) (= snapshots@0 (store snapshots (|val#Fraction_5603_5604| second_s) (store (select snapshots (|val#Fraction_5603_5604| second_s)) (|id#Fraction_5648_35| (|val#One_8419| second_perm)) (StampedValue inline$read_s$0$k@0 inline$read_s$0$v@0))))) (and (= snapshots@2 snapshots@0) (= (ControlFlow 0 6) 5))) inline$read_s$0$anon3_correct)))
(let ((inline$read_s$0$anon0_correct  (=> (and (Trigger_read_s_v inline$read_s$0$v@0) (Trigger_read_s_k inline$read_s$0$k@0)) (and (=> (= (ControlFlow 0 8) 6) inline$read_s$0$anon5_Then_correct) (=> (= (ControlFlow 0 8) 7) inline$read_s$0$anon5_Else_correct)))))
(let ((inline$Send$0$anon0_correct  (=> (and (and (= inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2 (Cell_6356_6358 (|val#One_6299| first_one_s) first_snapshot)) (not (select (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2)))) (and (= contents@0 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2) (|val#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2)))) (= (ControlFlow 0 9) 8))) inline$read_s$0$anon0_correct)))
(let ((inline$Send$0$Entry_correct  (=> (and (and (= ((_ map =>) (store ((as const (Array T@Fraction_5648_35 Bool)) false) (|val#One_8419| second_perm) true) ((_ map (= (Int Int) Bool)) skolemConstant0 ((as const (Array T@Fraction_5648_35 Int)) 0))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= ((_ map =>) (|val#Set_5987| pSet) ((_ map (= (Int Int) Bool)) skolemConstant0 ((as const (Array T@Fraction_5648_35 Int)) 1))) ((as const (Array T@Fraction_5648_35 Bool)) true))) (and (= ((_ map =>) (store ((as const (Array T@Fraction_5603_5604 Bool)) false) (|val#One_6299| first_one_s) true) ((_ map (= (Int Int) Bool)) skolemConstant1 ((as const (Array T@Fraction_5603_5604 Int)) 0))) ((as const (Array T@Fraction_5603_5604 Bool)) true)) (= ((_ map =>) (|val#Set_6023| (|dom#Map_6023_6025| contents)) ((_ map (= (Int Int) Bool)) skolemConstant1 ((as const (Array T@Fraction_5603_5604 Int)) 1))) ((as const (Array T@Fraction_5603_5604 Bool)) true)))) (=> (and (and (= (|val#Map_6023_6025| contents) ((_ map (ite (Bool T@StampedValue T@StampedValue) T@StampedValue)) (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|val#Map_6023_6025| contents) ((as const (Array T@Fraction_5603_5604 (Array Int T@StampedValue))) Default_21335))) (= (|val#One_6299| first_one_s) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_s)) Send (Set_5604 (store (|val#Set_5604| (Set_5604 (store (|val#Set_5604| (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) Send true))) Receive true))))) (and (forall ((second_k Int) ) (!  (=> true (=> true (=> (> second_k (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))) (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= (|val#One_6299| (One_6299 second_s)) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| (One_6299 second_s))) Send (Set_5604 (store (|val#Set_5604| (Set_5604 (store (|val#Set_5604| (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) Send true))) Receive true))))))))
 :qid |unknown.0:0|
 :skolemid |47|
)) (forall ((second_k@@0 Int) ) (!  (=> true (=> true (=> (> second_k@@0 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))) (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))) (Set_5987 (|lambda#3| (|val#One_6299| (One_6299 second_s)) (Set_35 (|lambda#1| 1 n)) (Set_35 (|lambda#1| 1 n)))))))))
 :qid |unknown.0:0|
 :skolemid |48|
)))) (=> (and (and (and (forall ((second_k@@1 Int) ) (!  (=> true (=> true (=> (> second_k@@1 (|ts#StampedValue| (select mem (|id#Fraction_5648_35| (|val#One_8419| second_perm))))) (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true))))))
 :qid |unknown.0:0|
 :skolemid |49|
)) (=> true (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= (|val#One_6299| (One_6299 second_s)) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| (One_6299 second_s))) Send (Set_5604 (store (|val#Set_5604| (Set_5604 (store (|val#Set_5604| (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) Send true))) Receive true))))))) (and (=> true (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n)))))) (Set_5987 (|lambda#3| (|val#One_6299| (One_6299 second_s)) (Set_35 (|lambda#1| 1 n)) (Set_35 (|lambda#1| 1 n))))))) (=> true (=> (= ((_ map =>) (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)) (= ((_ map =>) (|val#Set_5987| (Set_5987 (|val#Set_5987| (Set_5987 (|lambda#0| second_s (Set_35 (|lambda#1| 1 n))))))) (|val#Set_5987| (Set_5987 (store (|val#Set_5987| pSet) (|val#One_8419| second_perm) true)))) ((as const (Array T@Fraction_5648_35 Bool)) true)))))) (and (and (<= 1 (|id#Fraction_5648_35| (|val#One_8419| second_perm))) (<= (|id#Fraction_5648_35| (|val#One_8419| second_perm)) n)) (= (ControlFlow 0 10) 9))) inline$Send$0$anon0_correct)))))
inline$Send$0$Entry_correct)))))))))))))
))
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort T@Value 0)
(declare-sort T@Loc_5601 0)
(declare-datatypes ((T@Vec_2306 0)) (((Vec_2306 (|contents#Vec_2306| (Array Int Int)) (|len#Vec_2306| Int) ) ) ))
(declare-datatypes ((T@Vec_5 0)) (((Vec_5 (|contents#Vec_5| (Array Int Bool)) (|len#Vec_5| Int) ) ) ))
(declare-datatypes ((T@One_7133 0)) (((One_7133 (|val#One_7133| T@Loc_5601) ) ) ))
(declare-datatypes ((T@Set_35 0)) (((Set_35 (|val#Set_35| (Array Int Bool)) ) ) ))
(declare-datatypes ((T@ChannelOp 0)) (((Send ) (Receive ) ) ))
(declare-datatypes ((T@Set_5604 0)) (((Set_5604 (|val#Set_5604| (Array T@ChannelOp Bool)) ) ) ))
(declare-datatypes ((T@Fraction_5603_5604 0)) (((Fraction_5603_5604 (|val#Fraction_5603_5604| T@Loc_5601) (|id#Fraction_5603_5604| T@ChannelOp) (|ids#Fraction_5603_5604| T@Set_5604) ) ) ))
(declare-datatypes ((T@One_6299 0)) (((One_6299 (|val#One_6299| T@Fraction_5603_5604) ) ) ))
(declare-datatypes ((T@Set_6023 0)) (((Set_6023 (|val#Set_6023| (Array T@Fraction_5603_5604 Bool)) ) ) ))
(declare-datatypes ((T@Fraction_5648_35 0)) (((Fraction_5648_35 (|val#Fraction_5648_35| T@Fraction_5603_5604) (|id#Fraction_5648_35| Int) (|ids#Fraction_5648_35| T@Set_35) ) ) ))
(declare-datatypes ((T@One_8419 0)) (((One_8419 (|val#One_8419| T@Fraction_5648_35) ) ) ))
(declare-datatypes ((T@Set_5987 0)) (((Set_5987 (|val#Set_5987| (Array T@Fraction_5648_35 Bool)) ) ) ))
(declare-datatypes ((T@read_s 0)) (((read_s (|s#read_s| T@Fraction_5603_5604) (|perm#read_s| T@One_8419) ) ) ))
(declare-datatypes ((T@Choice_Inv_s 0)) (((Choice_Inv_s_read_s (|read_s#Choice_Inv_s_read_s| T@read_s) ) ) ))
(declare-datatypes ((|T@main_s'| 0)) (((|main_s'| (|send#main_s'| T@Fraction_5603_5604) (|sps#main_s'| T@Set_5987) ) ) ))
(declare-datatypes ((T@action_main_s 0)) (((action_main_s (|send#action_main_s| T@Fraction_5603_5604) (|sps#action_main_s| T@Set_5987) ) ) ))
(declare-datatypes ((T@read_f 0)) (((read_f (|s#read_f| T@Fraction_5603_5604) (|perm#read_f| T@One_8419) ) ) ))
(declare-datatypes ((T@Choice_Inv_f 0)) (((Choice_Inv_f_read_f (|read_f#Choice_Inv_f_read_f| T@read_f) ) ) ))
(declare-datatypes ((|T@main_f'| 0)) (((|main_f'| (|send#main_f'| T@Fraction_5603_5604) (|sps#main_f'| T@Set_5987) ) ) ))
(declare-datatypes ((T@action_main_f 0)) (((action_main_f (|send#action_main_f| T@Fraction_5603_5604) (|sps#action_main_f| T@Set_5987) ) ) ))
(declare-datatypes ((T@StampedValue 0)) (((StampedValue (|ts#StampedValue| Int) (|value#StampedValue| T@Value) ) ) ))
(declare-datatypes ((T@Cell_6356_6358 0)) (((Cell_6356_6358 (|key#Cell_6356_6358| T@Fraction_5603_5604) (|val#Cell_6356_6358| (Array Int T@StampedValue)) ) ) ))
(declare-datatypes ((T@Map_6023_6025 0)) (((Map_6023_6025 (|dom#Map_6023_6025| T@Set_6023) (|val#Map_6023_6025| (Array T@Fraction_5603_5604 (Array Int T@StampedValue))) ) ) ))
(declare-fun Set_Size_6023 (T@Set_6023) Int)
(declare-fun Set_Size_5987 (T@Set_5987) Int)
(declare-fun Set_Size_35 (T@Set_35) Int)
(declare-fun Set_Size_5604 (T@Set_5604) Int)
(declare-fun |lambda#8| (T@Fraction_5603_5604 Int Int T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun |lambda#1| (Int Int) (Array Int Bool))
(declare-fun |lambda#0| (T@Fraction_5603_5604 T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun Identity () (Array Int Int))
(declare-fun |lambda#9| (T@Fraction_5603_5604 Int Int T@Fraction_5603_5604 T@Set_35) (Array T@read_f Bool))
(declare-fun |lambda#33| (T@Fraction_5603_5604 Int Int T@Fraction_5603_5604 T@Set_35) (Array T@read_s Bool))
(declare-fun Default_2306 () Int)
(declare-fun Default_5 () Bool)
(declare-fun |lambda#2| (T@Loc_5601 T@Set_5604 T@Set_5604) (Array T@Fraction_5603_5604 Bool))
(declare-fun |lambda#3| (T@Fraction_5603_5604 T@Set_35 T@Set_35) (Array T@Fraction_5648_35 Bool))
(declare-fun |lambda#53| (T@Fraction_5603_5604 T@Set_5987) (Array T@read_f Bool))
(declare-fun |lambda#55| (T@Fraction_5603_5604 T@Set_5987) (Array T@read_s Bool))
(declare-fun Choice_6023 ((Array T@Fraction_5603_5604 Bool)) T@Fraction_5603_5604)
(declare-fun Choice_2289 ((Array Int Bool)) Int)
(declare-fun Choice_9763 ((Array T@Fraction_5648_35 Bool)) T@Fraction_5648_35)
(declare-fun Choice_4318 ((Array T@ChannelOp Bool)) T@ChannelOp)
(declare-fun n () Int)
(assert (forall ((a T@Set_6023) (t T@Fraction_5603_5604) ) (! (= (Set_Size_6023 (Set_6023 (store (|val#Set_6023| a) t false))) (ite (select (|val#Set_6023| a) t) (- (Set_Size_6023 a) 1) (Set_Size_6023 a)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_6023 (store (|val#Set_6023| a) t false)))
)))
(assert (forall ((a@@0 T@Set_5987) (t@@0 T@Fraction_5648_35) ) (! (= (Set_Size_5987 (Set_5987 (store (|val#Set_5987| a@@0) t@@0 false))) (ite (select (|val#Set_5987| a@@0) t@@0) (- (Set_Size_5987 a@@0) 1) (Set_Size_5987 a@@0)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_5987 (store (|val#Set_5987| a@@0) t@@0 false)))
)))
(assert (forall ((a@@1 T@Set_35) (t@@1 Int) ) (! (= (Set_Size_35 (Set_35 (store (|val#Set_35| a@@1) t@@1 false))) (ite (select (|val#Set_35| a@@1) t@@1) (- (Set_Size_35 a@@1) 1) (Set_Size_35 a@@1)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_35 (store (|val#Set_35| a@@1) t@@1 false)))
)))
(assert (forall ((a@@2 T@Set_5604) (t@@2 T@ChannelOp) ) (! (= (Set_Size_5604 (Set_5604 (store (|val#Set_5604| a@@2) t@@2 false))) (ite (select (|val#Set_5604| a@@2) t@@2) (- (Set_Size_5604 a@@2) 1) (Set_Size_5604 a@@2)))
 :qid |basebpl.166:18|
 :skolemid |10|
 :pattern ( (Set_5604 (store (|val#Set_5604| a@@2) t@@2 false)))
)))
(assert (forall ((x T@Vec_2306) ) (! (>= (|len#Vec_2306| x) 0)
 :qid |basebpl.75:32|
 :skolemid |6|
 :pattern ( (|len#Vec_2306| x))
)))
(assert (forall ((x@@0 T@Vec_5) ) (! (>= (|len#Vec_5| x@@0) 0)
 :qid |basebpl.75:32|
 :skolemid |6|
 :pattern ( (|len#Vec_5| x@@0))
)))
(assert (forall ((|l#0| T@Fraction_5603_5604) (|l#1| Int) (|l#2| Int) (|l#3| T@Set_35) (x@@1 T@Fraction_5648_35) ) (! (= (select (|lambda#8| |l#0| |l#1| |l#2| |l#3|) x@@1)  (and (and (and (= (|val#Fraction_5648_35| x@@1) |l#0|) (<= |l#1| (|id#Fraction_5648_35| x@@1))) (<= (|id#Fraction_5648_35| x@@1) |l#2|)) (= (|ids#Fraction_5648_35| x@@1) |l#3|)))
 :qid |snapshotscattergatherbpl.201:25|
 :skolemid |339|
 :pattern ( (select (|lambda#8| |l#0| |l#1| |l#2| |l#3|) x@@1))
)))
(assert (= (Set_Size_6023 (Set_6023 ((as const (Array T@Fraction_5603_5604 Bool)) false))) 0))
(assert (= (Set_Size_5987 (Set_5987 ((as const (Array T@Fraction_5648_35 Bool)) false))) 0))
(assert (= (Set_Size_35 (Set_35 ((as const (Array Int Bool)) false))) 0))
(assert (= (Set_Size_5604 (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) 0))
(assert (forall ((a@@3 T@Set_6023) (b T@Set_6023) ) (! (= (+ (Set_Size_6023 (Set_6023 ((_ map or) (|val#Set_6023| a@@3) (|val#Set_6023| b)))) (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@3) (|val#Set_6023| b))))) (+ (Set_Size_6023 a@@3) (Set_Size_6023 b)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_6023 ((_ map or) (|val#Set_6023| a@@3) (|val#Set_6023| b))))
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@3) (|val#Set_6023| b))))
)))
(assert (forall ((a@@4 T@Set_5987) (b@@0 T@Set_5987) ) (! (= (+ (Set_Size_5987 (Set_5987 ((_ map or) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0)))) (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))) (+ (Set_Size_5987 a@@4) (Set_Size_5987 b@@0)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_5987 ((_ map or) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@4) (|val#Set_5987| b@@0))))
)))
(assert (forall ((a@@5 T@Set_35) (b@@1 T@Set_35) ) (! (= (+ (Set_Size_35 (Set_35 ((_ map or) (|val#Set_35| a@@5) (|val#Set_35| b@@1)))) (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))) (+ (Set_Size_35 a@@5) (Set_Size_35 b@@1)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_35 ((_ map or) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@5) (|val#Set_35| b@@1))))
)))
(assert (forall ((a@@6 T@Set_5604) (b@@2 T@Set_5604) ) (! (= (+ (Set_Size_5604 (Set_5604 ((_ map or) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2)))) (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))) (+ (Set_Size_5604 a@@6) (Set_Size_5604 b@@2)))
 :qid |basebpl.172:18|
 :skolemid |12|
 :pattern ( (Set_5604 ((_ map or) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@6) (|val#Set_5604| b@@2))))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (x@@2 Int) ) (! (= (select (|lambda#1| |l#0@@0| |l#1@@0|) x@@2)  (and (<= |l#0@@0| x@@2) (<= x@@2 |l#1@@0|)))
 :qid |snapshotscattergatherbpl.61:40|
 :skolemid |336|
 :pattern ( (select (|lambda#1| |l#0@@0| |l#1@@0|) x@@2))
)))
(assert (forall ((a@@7 T@Set_6023) (t@@3 T@Fraction_5603_5604) ) (! (= (Set_Size_6023 (Set_6023 (store (|val#Set_6023| a@@7) t@@3 true))) (ite (select (|val#Set_6023| a@@7) t@@3) (Set_Size_6023 a@@7) (+ (Set_Size_6023 a@@7) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_6023 (store (|val#Set_6023| a@@7) t@@3 true)))
)))
(assert (forall ((a@@8 T@Set_5987) (t@@4 T@Fraction_5648_35) ) (! (= (Set_Size_5987 (Set_5987 (store (|val#Set_5987| a@@8) t@@4 true))) (ite (select (|val#Set_5987| a@@8) t@@4) (Set_Size_5987 a@@8) (+ (Set_Size_5987 a@@8) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_5987 (store (|val#Set_5987| a@@8) t@@4 true)))
)))
(assert (forall ((a@@9 T@Set_35) (t@@5 Int) ) (! (= (Set_Size_35 (Set_35 (store (|val#Set_35| a@@9) t@@5 true))) (ite (select (|val#Set_35| a@@9) t@@5) (Set_Size_35 a@@9) (+ (Set_Size_35 a@@9) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_35 (store (|val#Set_35| a@@9) t@@5 true)))
)))
(assert (forall ((a@@10 T@Set_5604) (t@@6 T@ChannelOp) ) (! (= (Set_Size_5604 (Set_5604 (store (|val#Set_5604| a@@10) t@@6 true))) (ite (select (|val#Set_5604| a@@10) t@@6) (Set_Size_5604 a@@10) (+ (Set_Size_5604 a@@10) 1)))
 :qid |basebpl.164:18|
 :skolemid |9|
 :pattern ( (Set_5604 (store (|val#Set_5604| a@@10) t@@6 true)))
)))
(assert (forall ((|l#0@@1| T@Fraction_5603_5604) (|l#1@@1| T@Set_35) (x@@3 T@Fraction_5648_35) ) (! (= (select (|lambda#0| |l#0@@1| |l#1@@1|) x@@3)  (and (and (= (|val#Fraction_5648_35| x@@3) |l#0@@1|) (= (|ids#Fraction_5648_35| x@@3) |l#1@@1|)) (select (|val#Set_35| (|ids#Fraction_5648_35| x@@3)) (|id#Fraction_5648_35| x@@3))))
 :qid |snapshotscattergatherbpl.55:38|
 :skolemid |335|
 :pattern ( (select (|lambda#0| |l#0@@1| |l#1@@1|) x@@3))
)))
(assert (forall ((a@@11 T@Set_6023) (b@@3 T@Set_6023) ) (! (= (Set_Size_6023 a@@11) (+ (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@11) ((_ map not) (|val#Set_6023| b@@3))))) (Set_Size_6023 (Set_6023 ((_ map and) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@11) ((_ map not) (|val#Set_6023| b@@3)))))
 :pattern ( (Set_6023 ((_ map and) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))
 :pattern ( (Set_6023 ((_ map or) (|val#Set_6023| a@@11) (|val#Set_6023| b@@3))))
)))
(assert (forall ((a@@12 T@Set_5987) (b@@4 T@Set_5987) ) (! (= (Set_Size_5987 a@@12) (+ (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@12) ((_ map not) (|val#Set_5987| b@@4))))) (Set_Size_5987 (Set_5987 ((_ map and) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@12) ((_ map not) (|val#Set_5987| b@@4)))))
 :pattern ( (Set_5987 ((_ map and) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))
 :pattern ( (Set_5987 ((_ map or) (|val#Set_5987| a@@12) (|val#Set_5987| b@@4))))
)))
(assert (forall ((a@@13 T@Set_35) (b@@5 T@Set_35) ) (! (= (Set_Size_35 a@@13) (+ (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@13) ((_ map not) (|val#Set_35| b@@5))))) (Set_Size_35 (Set_35 ((_ map and) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@13) ((_ map not) (|val#Set_35| b@@5)))))
 :pattern ( (Set_35 ((_ map and) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))
 :pattern ( (Set_35 ((_ map or) (|val#Set_35| a@@13) (|val#Set_35| b@@5))))
)))
(assert (forall ((a@@14 T@Set_5604) (b@@6 T@Set_5604) ) (! (= (Set_Size_5604 a@@14) (+ (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@14) ((_ map not) (|val#Set_5604| b@@6))))) (Set_Size_5604 (Set_5604 ((_ map and) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))))
 :qid |basebpl.168:18|
 :skolemid |11|
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@14) ((_ map not) (|val#Set_5604| b@@6)))))
 :pattern ( (Set_5604 ((_ map and) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))
 :pattern ( (Set_5604 ((_ map or) (|val#Set_5604| a@@14) (|val#Set_5604| b@@6))))
)))
(assert (forall ((x@@4 Int) ) (! (= (select Identity x@@4) x@@4)
 :qid |basebpl.64:15|
 :skolemid |4|
)))
(assert (forall ((|l#0@@2| T@Fraction_5603_5604) (|l#1@@2| Int) (|l#2@@0| Int) (|l#3@@0| T@Fraction_5603_5604) (|l#4| T@Set_35) (pa T@read_f) ) (! (= (select (|lambda#9| |l#0@@2| |l#1@@2| |l#2@@0| |l#3@@0| |l#4|) pa)  (and (and (and (and (= (|s#read_f| pa) |l#0@@2|) (<= |l#1@@2| (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))))) (<= (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#2@@0|)) (= (|val#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#3@@0|)) (= (|ids#Fraction_5648_35| (|val#One_8419| (|perm#read_f| pa))) |l#4|)))
 :qid |snapshotscattergatherbpl.201:25|
 :skolemid |340|
 :pattern ( (select (|lambda#9| |l#0@@2| |l#1@@2| |l#2@@0| |l#3@@0| |l#4|) pa))
)))
(assert (forall ((|l#0@@3| T@Fraction_5603_5604) (|l#1@@3| Int) (|l#2@@1| Int) (|l#3@@1| T@Fraction_5603_5604) (|l#4@@0| T@Set_35) (pa@@0 T@read_s) ) (! (= (select (|lambda#33| |l#0@@3| |l#1@@3| |l#2@@1| |l#3@@1| |l#4@@0|) pa@@0)  (and (and (and (and (= (|s#read_s| pa@@0) |l#0@@3|) (<= |l#1@@3| (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))))) (<= (|id#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#2@@1|)) (= (|val#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#3@@1|)) (= (|ids#Fraction_5648_35| (|val#One_8419| (|perm#read_s| pa@@0))) |l#4@@0|)))
 :qid |snapshotscattergatherbpl.299:25|
 :skolemid |341|
 :pattern ( (select (|lambda#33| |l#0@@3| |l#1@@3| |l#2@@1| |l#3@@1| |l#4@@0|) pa@@0))
)))
(assert (forall ((x@@5 T@Vec_2306) ) (! (= ((_ map (ite (Bool Int Int) Int)) ((_ map and) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) 0) Identity) ((_ map not) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) (+ 0 (|len#Vec_2306| x@@5))) Identity))) ((as const (Array Int Int)) Default_2306) (|contents#Vec_2306| x@@5)) ((as const (Array Int Int)) Default_2306))
 :qid |basebpl.74:32|
 :skolemid |5|
 :pattern ( (|len#Vec_2306| x@@5))
 :pattern ( (|contents#Vec_2306| x@@5))
)))
(assert (forall ((x@@6 T@Vec_5) ) (! (= ((_ map (ite (Bool Bool Bool) Bool)) ((_ map and) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) 0) Identity) ((_ map not) ((_ map (<= (Int Int) Int)) ((as const (Array Int Int)) (+ 0 (|len#Vec_5| x@@6))) Identity))) ((as const (Array Int Bool)) Default_5) (|contents#Vec_5| x@@6)) ((as const (Array Int Bool)) Default_5))
 :qid |basebpl.74:32|
 :skolemid |5|
 :pattern ( (|len#Vec_5| x@@6))
 :pattern ( (|contents#Vec_5| x@@6))
)))
(assert (forall ((|l#0@@4| T@Loc_5601) (|l#1@@4| T@Set_5604) (|l#2@@2| T@Set_5604) (piece T@Fraction_5603_5604) ) (! (= (select (|lambda#2| |l#0@@4| |l#1@@4| |l#2@@2|) piece)  (and (and (= (|val#Fraction_5603_5604| piece) |l#0@@4|) (select (|val#Set_5604| |l#1@@4|) (|id#Fraction_5603_5604| piece))) (= (|ids#Fraction_5603_5604| piece) |l#2@@2|)))
 :qid |basebpl.303:67|
 :skolemid |337|
 :pattern ( (select (|lambda#2| |l#0@@4| |l#1@@4| |l#2@@2|) piece))
)))
(assert (forall ((|l#0@@5| T@Fraction_5603_5604) (|l#1@@5| T@Set_35) (|l#2@@3| T@Set_35) (piece@@0 T@Fraction_5648_35) ) (! (= (select (|lambda#3| |l#0@@5| |l#1@@5| |l#2@@3|) piece@@0)  (and (and (= (|val#Fraction_5648_35| piece@@0) |l#0@@5|) (select (|val#Set_35| |l#1@@5|) (|id#Fraction_5648_35| piece@@0))) (= (|ids#Fraction_5648_35| piece@@0) |l#2@@3|)))
 :qid |basebpl.303:67|
 :skolemid |338|
 :pattern ( (select (|lambda#3| |l#0@@5| |l#1@@5| |l#2@@3|) piece@@0))
)))
(assert (forall ((|l#0@@6| T@Fraction_5603_5604) (|l#1@@6| T@Set_5987) (pa@@1 T@read_f) ) (! (= (select (|lambda#53| |l#0@@6| |l#1@@6|) pa@@1)  (and (= (|s#read_f| pa@@1) |l#0@@6|) (select (|val#Set_5987| |l#1@@6|) (|val#One_8419| (|perm#read_f| pa@@1)))))
 :qid |snapshotscattergatherbpl.141:39|
 :skolemid |342|
 :pattern ( (select (|lambda#53| |l#0@@6| |l#1@@6|) pa@@1))
)))
(assert (forall ((|l#0@@7| T@Fraction_5603_5604) (|l#1@@7| T@Set_5987) (pa@@2 T@read_s) ) (! (= (select (|lambda#55| |l#0@@7| |l#1@@7|) pa@@2)  (and (= (|s#read_s| pa@@2) |l#0@@7|) (select (|val#Set_5987| |l#1@@7|) (|val#One_8419| (|perm#read_s| pa@@2)))))
 :qid |snapshotscattergatherbpl.239:39|
 :skolemid |343|
 :pattern ( (select (|lambda#55| |l#0@@7| |l#1@@7|) pa@@2))
)))
(assert (forall ((a@@15 T@Set_6023) ) (!  (or (= a@@15 (Set_6023 ((as const (Array T@Fraction_5603_5604 Bool)) false))) (< 0 (Set_Size_6023 a@@15)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@16 T@Set_5987) ) (!  (or (= a@@16 (Set_5987 ((as const (Array T@Fraction_5648_35 Bool)) false))) (< 0 (Set_Size_5987 a@@16)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@17 T@Set_35) ) (!  (or (= a@@17 (Set_35 ((as const (Array Int Bool)) false))) (< 0 (Set_Size_35 a@@17)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@18 T@Set_5604) ) (!  (or (= a@@18 (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) (< 0 (Set_Size_5604 a@@18)))
 :qid |basebpl.160:18|
 :skolemid |7|
)))
(assert (forall ((a@@19 (Array T@Fraction_5603_5604 Bool)) ) (!  (or (= a@@19 ((as const (Array T@Fraction_5603_5604 Bool)) false)) (select a@@19 (Choice_6023 a@@19)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_6023 a@@19))
)))
(assert (forall ((a@@20 (Array Int Bool)) ) (!  (or (= a@@20 ((as const (Array Int Bool)) false)) (select a@@20 (Choice_2289 a@@20)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_2289 a@@20))
)))
(assert (forall ((a@@21 (Array T@Fraction_5648_35 Bool)) ) (!  (or (= a@@21 ((as const (Array T@Fraction_5648_35 Bool)) false)) (select a@@21 (Choice_9763 a@@21)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_9763 a@@21))
)))
(assert (forall ((a@@22 (Array T@ChannelOp Bool)) ) (!  (or (= a@@22 ((as const (Array T@ChannelOp Bool)) false)) (select a@@22 (Choice_4318 a@@22)))
 :qid |basebpl.236:18|
 :skolemid |13|
 :pattern ( (Choice_4318 a@@22))
)))
(assert (>= n 1))
(declare-fun ControlFlow (Int Int) Int)
(declare-fun mem () (Array Int T@StampedValue))
(declare-fun second_perm () T@One_8419)
(declare-fun second_s () T@Fraction_5603_5604)
(declare-fun pSet@2 () T@Set_5987)
(declare-fun snapshots@2 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun snapshots () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun pSet () T@Set_5987)
(declare-fun contents@2 () T@Map_6023_6025)
(declare-fun contents () T@Map_6023_6025)
(declare-fun first_one_s () T@One_6299)
(declare-fun first_snapshot () (Array Int T@StampedValue))
(declare-fun inline$read_s$0$v@0 () T@Value)
(declare-fun inline$read_s$0$k@0 () Int)
(declare-fun pSet@0 () T@Set_5987)
(declare-fun contents@0 () T@Map_6023_6025)
(declare-fun inline$read_s$0$pieces@1 () T@Set_5987)
(declare-fun pSet@1 () T@Set_5987)
(declare-fun inline$read_s$0$one_s@1 () T@One_6299)
(declare-fun inline$read_s$0$inline$Fractions_To_One_9245_198$0$ids@1 () T@Set_35)
(declare-fun inline$read_s$0$inline$Send$0$snapshot@1 () (Array Int T@StampedValue))
(declare-fun inline$read_s$0$inline$Cell_Pack_6465_6466$0$c@2 () T@Cell_6356_6358)
(declare-fun contents@1 () T@Map_6023_6025)
(declare-fun snapshots@1 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun snapshots@0 () (Array T@Loc_5601 (Array Int T@StampedValue)))
(declare-fun Trigger_read_s_v (T@Value) Bool)
(declare-fun Trigger_read_s_k (Int) Bool)
(declare-fun inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2 () T@Cell_6356_6358)
(declare-fun skolemConstant0 () (Array T@Fraction_5648_35 Int))
(declare-fun skolemConstant1 () (Array T@Fraction_5603_5604 Int))
(declare-fun Default_21335 () (Array Int T@StampedValue))
; Valid

(push 1)
(declare-fun inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$l@2 () T@One_6299)
(declare-fun contents@1 () T@Map_6023_6025)
(declare-fun second_one_s () T@One_6299)
(declare-fun second_snapshot () (Array Int T@StampedValue))
(declare-fun first_one_r () T@One_6299)
(declare-fun inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$v@2 () (Array Int T@StampedValue))
(declare-fun inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2 () T@Cell_6356_6358)
(declare-fun contents@0 () T@Map_6023_6025)
(declare-fun inline$action_Receive$0$s@1 () T@Fraction_5603_5604)
(declare-fun inline$action_Receive$0$cell@1 () T@Cell_6356_6358)
(set-info :boogie-vc-id Civl_CommutativityChecker_action_Receive_Send)
(set-option :timeout 0)
(set-option :rlimit 0)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(assert (not
 (=> (= (ControlFlow 0 0) 5) (let ((inline$Send$0$Return_correct  (=> (= (ControlFlow 0 2) (- 0 1)) (=> (and (exists ((Civl_partition_Fraction_5603_5604 (Array T@Fraction_5603_5604 Int)) ) (!  (and (= ((_ map =>) (store ((as const (Array T@Fraction_5603_5604 Bool)) false) (|val#One_6299| inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$l@2) true) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604 ((as const (Array T@Fraction_5603_5604 Int)) 0))) ((as const (Array T@Fraction_5603_5604 Bool)) true)) (= ((_ map =>) (|val#Set_6023| (|dom#Map_6023_6025| contents@1)) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604 ((as const (Array T@Fraction_5603_5604 Int)) 1))) ((as const (Array T@Fraction_5603_5604 Bool)) true)))
 :qid |unknown.0:0|
 :skolemid |75|
)) (exists ((Civl_partition_Fraction_5603_5604@@0 (Array T@Fraction_5603_5604 Int)) ) (!  (and (= ((_ map =>) (store ((as const (Array T@Fraction_5603_5604 Bool)) false) (|val#One_6299| inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$l@2) true) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604@@0 ((as const (Array T@Fraction_5603_5604 Int)) 0))) ((as const (Array T@Fraction_5603_5604 Bool)) true)) (= ((_ map =>) (|val#Set_6023| (|dom#Map_6023_6025| contents@1)) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604@@0 ((as const (Array T@Fraction_5603_5604 Int)) 1))) ((as const (Array T@Fraction_5603_5604 Bool)) true)))
 :qid |unknown.0:0|
 :skolemid |76|
))) (and (and (and (select (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)))))) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r)))) (= contents@1 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)))))) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))) false)) (store (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot))))) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))) Default_21335)))) (= inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$l@2 (One_6299 (|key#Cell_6356_6358| (Cell_6356_6358 (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))) (select (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot))))) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))))))))) (= inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$v@2 (|val#Cell_6356_6358| (Cell_6356_6358 (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))) (select (|val#Map_6023_6025| (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) true)) (store (|val#Map_6023_6025| contents) (|key#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (|val#Cell_6356_6358| (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot))))) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))))))))))))
(let ((inline$Send$0$anon0_correct  (=> (and (and (= inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2 (Cell_6356_6358 (|val#One_6299| second_one_s) second_snapshot)) (not (select (|val#Set_6023| (|dom#Map_6023_6025| contents@0)) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2)))) (and (= contents@1 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents@0)) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2) true)) (store (|val#Map_6023_6025| contents@0) (|key#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2) (|val#Cell_6356_6358| inline$Send$0$inline$Cell_Pack_6465_6466$0$c@2)))) (= (ControlFlow 0 3) 2))) inline$Send$0$Return_correct)))
(let ((inline$action_Receive$0$anon0_correct  (=> (= inline$action_Receive$0$s@1 (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r)))) (=> (and (select (|val#Set_6023| (|dom#Map_6023_6025| contents)) inline$action_Receive$0$s@1) (= inline$action_Receive$0$cell@1 (Cell_6356_6358 inline$action_Receive$0$s@1 (select (|val#Map_6023_6025| contents) inline$action_Receive$0$s@1)))) (=> (and (and (= contents@0 (Map_6023_6025 (Set_6023 (store (|val#Set_6023| (|dom#Map_6023_6025| contents)) inline$action_Receive$0$s@1 false)) (store (|val#Map_6023_6025| contents) inline$action_Receive$0$s@1 Default_21335))) (= inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$l@2 (One_6299 (|key#Cell_6356_6358| inline$action_Receive$0$cell@1)))) (and (= inline$action_Receive$0$inline$Cell_Unpack_6988_6989$0$v@2 (|val#Cell_6356_6358| inline$action_Receive$0$cell@1)) (= (ControlFlow 0 4) 3))) inline$Send$0$anon0_correct)))))
(let ((inline$action_Receive$0$Entry_correct  (=> (and (exists ((Civl_partition_Fraction_5603_5604@@1 (Array T@Fraction_5603_5604 Int)) ) (!  (and (and (= ((_ map =>) (store ((as const (Array T@Fraction_5603_5604 Bool)) false) (|val#One_6299| first_one_r) true) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604@@1 ((as const (Array T@Fraction_5603_5604 Int)) 0))) ((as const (Array T@Fraction_5603_5604 Bool)) true)) (= ((_ map =>) (store ((as const (Array T@Fraction_5603_5604 Bool)) false) (|val#One_6299| second_one_s) true) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604@@1 ((as const (Array T@Fraction_5603_5604 Int)) 1))) ((as const (Array T@Fraction_5603_5604 Bool)) true))) (= ((_ map =>) (|val#Set_6023| (|dom#Map_6023_6025| contents)) ((_ map (= (Int Int) Bool)) Civl_partition_Fraction_5603_5604@@1 ((as const (Array T@Fraction_5603_5604 Int)) 2))) ((as const (Array T@Fraction_5603_5604 Bool)) true)))
 :qid |unknown.0:0|
 :skolemid |74|
)) (= (|val#Map_6023_6025| contents) ((_ map (ite (Bool T@StampedValue T@StampedValue) T@StampedValue)) (|val#Set_6023| (|dom#Map_6023_6025| contents)) (|val#Map_6023_6025| contents) ((as const (Array T@Fraction_5603_5604 (Array Int T@StampedValue))) Default_21335)))) (=> (and (and (=> (select (|val#Set_6023| (|dom#Map_6023_6025| contents)) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r)))) (select (|val#Set_6023| (|dom#Map_6023_6025| contents)) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Send (|ids#Fraction_5603_5604| (|val#One_6299| first_one_r))))) (= (|val#One_6299| first_one_r) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| first_one_r)) Receive (Set_5604 (store (|val#Set_5604| (Set_5604 (store (|val#Set_5604| (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) Send true))) Receive true))))) (and (= (|val#One_6299| second_one_s) (Fraction_5603_5604 (|val#Fraction_5603_5604| (|val#One_6299| second_one_s)) Send (Set_5604 (store (|val#Set_5604| (Set_5604 (store (|val#Set_5604| (Set_5604 ((as const (Array T@ChannelOp Bool)) false))) Send true))) Receive true)))) (= (ControlFlow 0 5) 4))) inline$action_Receive$0$anon0_correct))))
inline$action_Receive$0$Entry_correct)))))
))
; Valid
