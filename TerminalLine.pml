/* CS17061, CS1805, CS18017, CS18020, CS18019 */

#define train 99; /* A train is identified by a constant */
#define p (len(Tunnel_1_2) < 2) /* A train is identified by a constant */
#define q (len(Tunnel_2_3) < 2) /* A premise for the ltl formulas*/
#define r (len(Tunnel_3_4) < 2) 
#define s (len(Tunnel_4_1) < 2)
#define t (len(Tunnel_1_2) == 0)
#define u (len(Tunnel_2_3) == 0)
#define v (len(Tunnel_3_4) == 0)
#define w (len(Tunnel_4_1) == 0)
chan Tunnel_1_2 = [2] of { byte }; /* Models tunnel between stations 1 and 2 */
chan Tunnel_2_3 = [2] of { byte }; /* Models tunnel between stations 2 and 3*/
chan Tunnel_3_4 = [2] of { byte }; /* Models tunnel between stations 3 and 4 */
chan Tunnel_4_1 = [2] of { byte }; /* Models tunnel between stations 4 and 1 */
chan SigBox_1_4 = [0] of { bit }; /* Channel between signal box 1 and 4 */
chan SigBox_2_1 = [0] of { bit };
chan SigBox_3_2 = [0] of { bit };
chan SigBox_4_3 = [0] of { bit };
chan in_SigBox_1 = [0] of { bit }; /* Local channel of signal box 1 */
chan out_SigBox_1 = [0] of { mtype }; /* Local channel of signal box 1 */
chan in_SigBox_2 = [0] of { bit };
chan out_SigBox_2 = [0] of { mtype };
chan in_SigBox_3 = [0] of { bit };
chan out_SigBox_3 = [0] of { mtype };
chan in_SigBox_4 = [0] of { bit };
chan out_SigBox_4 = [0] of { mtype };
mtype = {A,D,R};


proctype Station(chan in_track, out_track, in_SigBox, out_SigBox; byte train_cnt)
{
        bit signal = 0;
        do
        :: (train_cnt > 0) ->
                                if
                                :: signal == 0 -> out_SigBox!R; in_SigBox?signal;
                                :: signal == 1 -> out_SigBox!D;in_SigBox?signal;out_track!train;train_cnt--;
                                fi
		:: in_track?train-> out_SigBox!A;train_cnt++;
        od
}

init
{
        atomic
        {
        run Station(Tunnel_4_1, Tunnel_1_2,in_SigBox_1,out_SigBox_1,1);/* The process that models station */
        run Station(Tunnel_1_2, Tunnel_2_3,in_SigBox_2,out_SigBox_2,0);/* The process that models station */
        run Station(Tunnel_2_3, Tunnel_3_4,in_SigBox_3,out_SigBox_3,1);/* The process that models station */
        run Station(Tunnel_3_4, Tunnel_4_1,in_SigBox_4,out_SigBox_4,0);/* The process that models station */
        run SigBox(SigBox_1_4,SigBox_4_3,in_SigBox_4,out_SigBox_4);/* The process that models signal box */
        run SigBox(SigBox_2_1,SigBox_1_4,in_SigBox_1,out_SigBox_1);/* The process that models signal box */
        run SigBox(SigBox_3_2,SigBox_2_1,in_SigBox_2,out_SigBox_2);/* The process that models signal box */
        run SigBox(SigBox_4_3,SigBox_3_2,in_SigBox_3,out_SigBox_3);/* The process that models signal box */
        }                              
}

proctype SigBox(chan sigBox_in, sigBox_out, station_in, station_out)
{
        bit flag=1;
        mtype value;
        do
        :: station_out?value ->
                if
                :: value==A -> sigBox_out!1;
                :: value==R -> station_in!flag; flag = 0;
                :: value==D -> station_in!0; flag = 0;
                fi
        :: sigBox_in?flag -> flag= 1;
        od
}

active proctype monitor()
{
        assert(nfull(Tunnel_1_2) && nfull(Tunnel_2_3)&& nfull(Tunnel_3_4) && nfull(Tunnel_4_1));
}

/* Safety LTL formulae */
ltl p1
{
	[](p&&q&&r&&s)
}

/* Liveness LTL formulae */
ltl p2
{
	[]<>(t || u || v || w)
}