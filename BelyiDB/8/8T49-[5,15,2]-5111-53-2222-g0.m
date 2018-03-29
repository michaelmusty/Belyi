s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[5,15,2]-5111-53-2222-g0";
s`BelyiDBFilename := "8T49-[5,15,2]-5111-53-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 5, 15, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 8, 7, 5, 6, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 3, 8, 7, 5, 6, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 3, 8, 7, 5, 6, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 1, 6, 7, 8 ],
\[ 3, 8, 7, 5, 6, 4, 2, 1 ],
\[ 4, 8, 7, 1, 6, 5, 3, 2 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 8, 7, 5, 6, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 1, 6, 7, 8 ],
[ 3, 8, 7, 5, 6, 4, 2, 1 ],
[ 4, 8, 7, 1, 6, 5, 3, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
