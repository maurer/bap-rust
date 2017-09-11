//! This module provides `holmes` `Value` and `Type` status for selected binary analysis types, to
//! ease the use of this library in conjunction with `holmes`
use holmes::pg::dyn::values::ValueT;
use holmes::pg::dyn::types::TypeT;
use high::bitvector::BitVector;
use high::bil::Variable;
use basic::Arch;
use std::any::Any;
use std::sync::Arc;
use holmes::pg::RowIter;
use holmes::pg::dyn::{Type, Value};
use holmes::pg::dyn::values::ToValue;
use num::traits::FromPrimitive;
use std::error::Error;
use postgres::types::{ToSql, IsNull};
use rustc_serialize::json::{Decoder, Json};
use rustc_serialize::json;
use rustc_serialize::Decodable;

#[derive(Debug, Clone, Hash, PartialEq)]
/// This type is used to give a `holmes` `Type` to `bap::bitvector::BitVector`
pub struct BitVectorType;
impl TypeT for BitVectorType {
    fn name(&self) -> Option<&'static str> {
        Some("bitvector")
    }
    fn extract(&self, cols: &mut RowIter) -> Option<Value> {
        cols.next().map(
            |col| Arc::new(BitVector::new(&col)) as Value,
        )
    }
    fn repr(&self) -> &'static str {
        "bit varying"
    }
    typet_boiler!();
}

impl ValueT for BitVector {
    fn type_(&self) -> Type {
        Arc::new(BitVectorType)
    }
    fn get(&self) -> &Any {
        self as &Any
    }
    fn to_sql(&self) -> Vec<&ToSql> {
        vec![self.to_bitvec()]
    }
    valuet_boiler!();
}

impl ToValue for BitVector {
    fn to_value(self) -> Value {
        Arc::new(self)
    }
}

#[derive(Debug, Clone, Hash, PartialEq)]
/// This type is used to give a `holmes` `Type` to `bap::basic::Arch`
pub struct ArchType;
impl TypeT for ArchType {
    fn name(&self) -> Option<&'static str> {
        Some("arch")
    }
    fn extract(&self, cols: &mut RowIter) -> Option<Value> {
        cols.next().and_then(|col| {
            Arch::from_i16(col).map(|arch| Arc::new(arch) as Value)
        })
    }
    fn repr(&self) -> &'static str {
        "smallint"
    }
    typet_boiler!();
}

impl ValueT for Arch {
    fn type_(&self) -> Type {
        Arc::new(ArchType)
    }
    fn get(&self) -> &Any {
        self as &Any
    }
    fn to_sql(&self) -> Vec<&ToSql> {
        vec![self.i16_ref()]
    }
    valuet_boiler!();
}

impl ToValue for Arch {
    fn to_value(self) -> Value {
        Arc::new(self)
    }
}

#[derive(Debug, Clone, Hash, PartialEq)]
/// This represents the Holmes type for `Variable`
pub struct VarType;
impl TypeT for VarType {
    fn name(&self) -> Option<&'static str> {
        Some("var")
    }
    fn extract(&self, cols: &mut RowIter) -> Option<Value> {
        cols.next().map(|raw: Json| {
            let typed: Variable = {
                let mut decoder = Decoder::new(raw);
                Variable::decode(&mut decoder).unwrap()
            };
            Arc::new(typed) as Value
        })
    }
    fn repr(&self) -> &'static str {
        "jsonb"
    }
    typet_boiler!();
}
impl ValueT for Variable {
    fn type_(&self) -> Type {
        Arc::new(VarType)
    }
    fn get(&self) -> &Any {
        self as &Any
    }
    fn to_sql(&self) -> Vec<&ToSql> {
        vec![self]
    }
    valuet_boiler!();
}
impl ToSql for Variable {
    accepts!(::postgres::types::JSONB, ::postgres::types::JSON);
    to_sql_checked!();
    fn to_sql(
        &self,
        ty: &::postgres::types::Type,
        out: &mut Vec<u8>,
    ) -> Result<IsNull, Box<Error + Sync + Send>> {
        Json::from_str(&json::encode(self).unwrap())
            .unwrap()
            .to_sql(ty, out)
    }
}
