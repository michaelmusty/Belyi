s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T12-[6,4,3]-62-44-3311-g1";
s`BelyiDBFilename := "8T12-[6,4,3]-62-44-3311-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 4, 5, 6, 7, 8, 1, 2 ],
\[ 3, 2, 8, 5, 7, 6, 4, 1 ]:
 Order := 24 > |
[ 8, 5, 7, 6, 4, 1, 3, 2 ],
[ 7, 8, 1, 2, 3, 4, 5, 6 ],
[ 8, 2, 1, 7, 4, 6, 5, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 5, 7, 6, 4, 1, 3, 2 ],
\[ 7, 8, 1, 2, 3, 4, 5, 6 ],
\[ 8, 2, 1, 7, 4, 6, 5, 3 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 5, 7, 6, 4, 1, 3, 2 ],
\[ 7, 8, 1, 2, 3, 4, 5, 6 ],
\[ 8, 2, 1, 7, 4, 6, 5, 3 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 8, 5, 7, 6, 4, 1, 3, 2 ],
\[ 7, 8, 1, 2, 3, 4, 5, 6 ],
\[ 8, 2, 1, 7, 4, 6, 5, 3 ]:
 Order := 24 > |
[ 8, 5, 7, 6, 4, 1, 3, 2 ],
[ 7, 8, 1, 2, 3, 4, 5, 6 ],
[ 8, 2, 1, 7, 4, 6, 5, 3 ]
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
[ 8, 5, 7, 6, 4, 1, 3, 2 ],
[ 7, 8, 1, 2, 3, 4, 5, 6 ],
[ 8, 2, 1, 7, 4, 6, 5, 3 ]
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
