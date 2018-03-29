s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T14-[4,4,3]-44-44-3311-g1";
s`BelyiDBFilename := "8T14-[4,4,3]-44-44-3311-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 > |
[ 7, 5, 4, 2, 3, 1, 8, 6 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 3, 1, 2, 4, 7, 5, 6, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 5, 4, 2, 3, 1, 8, 6 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 3, 1, 2, 4, 7, 5, 6, 8 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 5, 4, 2, 3, 1, 8, 6 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 3, 1, 2, 4, 7, 5, 6, 8 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 7, 5, 4, 2, 3, 1, 8, 6 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 3, 1, 2, 4, 7, 5, 6, 8 ]:
 Order := 24 > |
[ 7, 5, 4, 2, 3, 1, 8, 6 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 3, 1, 2, 4, 7, 5, 6, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 > |
[ 7, 5, 4, 2, 3, 1, 8, 6 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 3, 1, 2, 4, 7, 5, 6, 8 ]
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
