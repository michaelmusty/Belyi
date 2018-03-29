s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[7,5,5]-71-5111-5111-g0";
s`BelyiDBFilename := "8T49-[7,5,5]-71-5111-5111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 5, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 7, 2, 8, 3, 4, 5, 6, 1 ],
[ 8, 1, 4, 2, 5, 6, 7, 3 ],
[ 1, 4, 3, 5, 6, 7, 2, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 2, 8, 3, 4, 5, 6, 1 ],
\[ 8, 1, 4, 2, 5, 6, 7, 3 ],
\[ 1, 4, 3, 5, 6, 7, 2, 8 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 2, 8, 3, 4, 5, 6, 1 ],
\[ 8, 1, 4, 2, 5, 6, 7, 3 ],
\[ 1, 4, 3, 5, 6, 7, 2, 8 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 7, 2, 8, 3, 4, 5, 6, 1 ],
\[ 8, 1, 4, 2, 5, 6, 7, 3 ],
\[ 1, 4, 3, 5, 6, 7, 2, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 7, 1, 3, 4, 5, 8, 6, 2 ],
[ 1, 2, 8, 3, 4, 5, 7, 6 ]
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
[ 7, 2, 8, 3, 4, 5, 6, 1 ],
[ 8, 1, 4, 2, 5, 6, 7, 3 ],
[ 1, 4, 3, 5, 6, 7, 2, 8 ]
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
