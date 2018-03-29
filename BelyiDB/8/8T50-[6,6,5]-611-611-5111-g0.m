s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,6,5]-611-611-5111-g0";
s`BelyiDBFilename := "8T50-[6,6,5]-611-611-5111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 1, 3, 4, 6, 7, 8, 2 ],
[ 1, 2, 8, 3, 4, 5, 6, 7 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 1, 3, 4, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 4, 5, 6, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 1, 3, 4, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 4, 5, 6, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 1, 3, 4, 6, 7, 8, 2 ],
\[ 1, 2, 8, 3, 4, 5, 6, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 1, 7, 8 ],
[ 6, 2, 3, 7, 4, 5, 8, 1 ],
[ 1, 8, 2, 3, 5, 6, 4, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 1, 3, 4, 6, 7, 8, 2 ],
[ 1, 2, 8, 3, 4, 5, 6, 7 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
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
