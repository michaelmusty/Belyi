s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T12-[3,4,3]-3311-44-3311-g0";
s`BelyiDBFilename := "8T12-[3,4,3]-3311-44-3311-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 3, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 > |
[ 8, 2, 1, 7, 4, 6, 5, 3 ],
[ 3, 4, 5, 6, 7, 8, 1, 2 ],
[ 1, 8, 6, 3, 5, 4, 2, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 2, 1, 7, 4, 6, 5, 3 ],
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 1, 8, 6, 3, 5, 4, 2, 7 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 2, 1, 7, 4, 6, 5, 3 ],
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 1, 8, 6, 3, 5, 4, 2, 7 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 8, 2, 1, 7, 4, 6, 5, 3 ],
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 1, 8, 6, 3, 5, 4, 2, 7 ]:
 Order := 24 > |
[ 3, 2, 8, 5, 7, 6, 4, 1 ],
[ 7, 8, 1, 2, 3, 4, 5, 6 ],
[ 2, 4, 3, 1, 6, 8, 7, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 > |
[ 8, 2, 1, 7, 4, 6, 5, 3 ],
[ 3, 4, 5, 6, 7, 8, 1, 2 ],
[ 1, 8, 6, 3, 5, 4, 2, 7 ]
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
